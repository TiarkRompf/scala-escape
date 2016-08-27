package scala.tools.escape

import scala.tools.nsc.transform._
import scala.tools.nsc.symtab._
import scala.tools.nsc.plugins._

import scala.language.postfixOps

/**
 * Check that `@safe` symbols do not escape their defining scope.
 */
abstract class EscTransform extends PluginComponent with Transform with
  TypingTransformers with EscUtils {
  // inherits abstract value `global` and class `Phase` from Transform

  import global._                  // the global environment
  import definitions._             // standard classes and methods
  import typer.atOwner             // methods to type trees

  override def description = "Escape check phase"

  /** the following two members override abstract members in Transform */
  val phaseName: String = "escape"

  protected def newTransformer(unit: CompilationUnit): Transformer =
    new EscTransformer(unit)

  class EscTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {

    def dominates(a: Symbol, b: Symbol) = 
      b.owner.owner.hasTransOwner(a.owner)
    def dominates(a: Symbol, bs: Set[Symbol]) = 
      bs.forall(_.owner.owner.hasTransOwner(a.owner))

    // FIXME: proper sym lookup
    def isSndFun(tpe: Type) = tpe.toString.startsWith("scala.util.escape.->") || tpe.toString.startsWith("->")
    //def isSndSym(s: Symbol) = !isFstSym(s) //s.hasAnnotation(MarkerLocal)
    def isFstSym(s: Symbol): Boolean = symMode(s) <:< FstMode
    def symMode(s:Symbol) = 
      s.getAnnotation(MarkerLocal) match { 
        case None => FstMode 
        case Some(s) => s.atp.typeArgs(0)
      }

    lazy val FstMode = NothingTpe
    lazy val SndMode = AnyTpe
/*
    TODO:

      + check inheritance
      + abstract over mode
      - objects:
          - what is the story for @local this?
          - can one call methods on @local objects?

*/

    // in general: 1st class is more specific than 2nd class
    def traverse(tree: Tree, m: Type, boundary: List[Symbol]): Unit = {
      curTree = tree
      tree match {
      case Literal(x) =>
      case Ident(x) =>
        if (!isFstSym(tree.symbol)) {
          if (!(symMode(tree.symbol) <:< m)) {
            // 2nd class vars are not 1st class
            reporter.error(tree.pos, tree.symbol + " cannot be used as 1st class value @local["+m+"]")
          } else {
            // cannot reach beyond 1st class boundary
            for (b <- boundary) {
              if (!tree.symbol.hasTransOwner(b))
                if (!(symMode(tree.symbol) <:< symMode(b)))
                  reporter.error(tree.pos, tree.symbol + s" cannot be used inside $b")
            }
          }
        }

      case Select(qual, name) =>
        // TODO: is 2nd class ok here?
        traverse(qual,SndMode,boundary)

      case Apply(fun, args) =>
        traverse(fun,SndMode,boundary) // function is always 2nd class
        dprintln(s"--- apply ")

        dprintln(fun.symbol.name)
        dprintln(fun.symbol.owner.name)
        dprintln(fun.symbol.throwsAnnotations.map(_.tpe))



        // find out mode to use for each argument (1st or 2nd)
        val modes = fun.tpe match {
          case mt @ MethodType(params,restpe) =>
            fun match { 
              case Apply(TypeApply(Select(qual,name),_),_) => // TBD correct or need to apply type manually?
                params.map(s => symMode(s).asSeenFrom(qual.tpe, fun.symbol.owner))
              case TypeApply(Select(qual,name),_) => // TBD correct or need to apply type manually?
                params.map(s => symMode(s).asSeenFrom(qual.tpe, fun.symbol.owner))
              case Select(qual,name) =>
                params.map(s => symMode(s).asSeenFrom(qual.tpe, fun.symbol.owner))
              case Ident(_) =>
                params.map(s => symMode(s))
              case _ =>
                //println("---> other: "+ fun.getClass + "/"+fun +"/"+fun.symbol.owner)
                params.map(s => symMode(s))
            }
          case _ => Nil
        }
        // check argument expressions according to mode
        // for varargs, assume 1st class (pad to args.length)
        map2(args,modes.padTo(args.length,FstMode))((a,m) => traverse(a,m,boundary))

      case TypeApply(fun, args) => 
        traverse(fun,SndMode,boundary) // function is always 2nd class

      case Assign(lhs, rhs) =>
        // TODO: what if var is @local?
        //traverse(rhs,symMode(tree.symbol),boundary)
        traverse(rhs,FstMode,boundary)

      case If(cond, thenp, elsep) =>
        traverse(cond,SndMode,boundary)
        traverse(thenp,m,boundary)
        traverse(elsep,m,boundary)

      case LabelDef(name, params, rhs) =>
        traverse(rhs,m,boundary)

      case TypeDef(mods, name, tparams, rhs) =>
        traverse(rhs,FstMode,boundary) // 1?

      case ValDef(mods, name, tpt, rhs) =>
        //println(s"--- recurse $m val: ${tree.symbol}")
        traverse(rhs,symMode(tree.symbol),boundary) // need to check if val is 1st or 2nd

      case DefDef(mods, name, tparams, vparamss, tpt, rhs) if tree.symbol.isConstructor =>
        // do nothing

      case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        //println(s"--- recurse $m def: ${tree.symbol}")

        // if this def is 1st class, take it as new boundary
        val boundary1 = tree.symbol::boundary
        // function bodies are always 1st class
        traverse(rhs,FstMode,boundary1)

      case Function(vparams, body) =>
        //println(s"--- recurse $m func: ${tree.tpe}")

        // if this def is 1st class, take it as new boundary
        tree.symbol.addAnnotation(newLocalMarker(m))
        val boundary1 = tree.symbol::boundary
        // function bodies are always 1st class
        traverse(body,FstMode,boundary1)


      // Look for SAM closure corresponding to `->`
      // We treat this case specially to make the closure argument @local
      /*
      {
        def apply$body(x: Int): Int = 2.*(x);
        @SerialVersionUID(0) final class $anonfun extends AnyRef with scala.util.escape.->[Int,Int] with Serializable {
          def <init>(): <$anon: Int => Int> = {
            $anonfun.super.<init>();
            ()
          };
          final override <synthetic> def apply(x: Int): Int = apply$body(x)
        };
        new $anonfun()
      }
      */
      case Block(List(
        bd @ DefDef(bmods, bname, tparams, bvparamss, btpt, brhs), /* body */
        cd @ ClassDef(mods, name, params, 
          Template(parents, self, List(
            DefDef(_,_,_,_,_,_),   /* <init> */
            DefDef(_,_,_,_,_,_)))) /* <apply> */
        ),
        Apply(Select(New(tpt),_/*<init>*/),_)) 
        if tpt.symbol == cd.symbol
        && parents.exists(t => isSndFun(t.tpe))
        =>
          // find 2nd class function prototype
          val Some(base) = parents.find(t => isSndFun(t.tpe))

          // extract 'classiness' FIXME: proper sym lookup
          val mode = if (base.tpe.toString.startsWith("scala.util.escape.->*"))
            base.tpe.typeArgs(0) // e.g. `->*`[ReadOnly,File,Int]
          else // `->`
            SndMode

          // add @local annotation to closure parameter
          val List(List(bvparam)) = bvparamss
          bvparam.symbol.addAnnotation(newLocalMarker(mode))

          // if this def is 1st class, take it as new boundary
          bd.symbol.addAnnotation(newLocalMarker(m))
          val boundary1 = bd.symbol::boundary

          // go and check body
          traverse(brhs,FstMode,boundary)


      case Block(stats, expr) =>
        stats.foreach(s => traverse(s,SndMode,boundary))
        traverse(expr,m,boundary)

      case This(qual) => // TODO: ok?

      case TypeTree() => // TODO: what?

      case New(tpt) =>   // TODO: what?

      case Typed(expr, tpt) =>   // TODO: what?
        traverse(expr,m,boundary)

      case EmptyTree =>

      case Super(qual, mix) =>
        traverse(qual,FstMode,boundary) // 1?

      case Throw(expr) =>
        traverse(expr,FstMode,boundary) // 

      case Return(expr) =>
        traverse(expr,FstMode,boundary) // escapes

      case Import(expr, selectors) =>
        traverse(expr,FstMode,boundary) // 1?

      case Match(selector, cases) =>        
        traverse(selector,FstMode,boundary)
        cases foreach { case cd @ CaseDef(pat, guard, body) =>
          traverse(body,m,boundary)
        }

      case Try(block, catches, finalizer) =>
        traverse(block,m,boundary)
        catches foreach { case cd @ CaseDef(pat, guard, body) =>
          traverse(body,m,boundary)
        }
        traverse(finalizer,m,boundary)

      case ClassDef(mods, name, params, impl) =>
        //println(s"--- recurse $m class: ${tree.symbol}")
        atOwner(tree.symbol) { 
          traverse(impl,FstMode,boundary)
        }

      case Template(parents, self, body) =>
        atOwner(currentOwner) {
        // perform a crude RefChecks run:
        // subclasses are only allowed to _add_ @local annotations on
        // method parameters, not to remove them.

        // TODO: what about annotations on members directly,
        // not on method arguments?

            def checkOverride(pair: SymbolPair) = {
              val member   = pair.low
              val other    = pair.high
              def argModes(tpe: Type) = tpe match {
                case mt @ MethodType(params,restpe) => params.map(symMode)
                case _ => Nil
              }
              // member 2, other 1 is OK, but not vice versa
              val memberM = argModes(member.tpe)
              val otherM = argModes(other.tpe)

              def compare(a: Type, b: Type) = {
                val a1 = a.asSeenFrom(pair.rootType,a.typeSymbol.owner)
                val b1 = b.asSeenFrom(pair.rootType,b.typeSymbol.owner)
                val res = a1 <:< b1
                //println(s"$a1 <:<: $b1 = $res")
                res
              }

              val allOK = memberM.length == otherM.length && map2(otherM,memberM)(compare).forall(x=>x)
              if (!allOK) {
                val fullmsg = "overriding " + pair.high.fullLocationString + " with " + pair.low.fullLocationString + ":\n" +
                s"some @local annotations on arguments have been dropped"
                reporter.error(member.pos, fullmsg)
              }
              // require that either both have @local annotation on member or none
              // TODO: what is sensible here?
              if (symMode(member) != symMode(other)) {
                val fullmsg = "overriding " + pair.high.fullLocationString + " with " + pair.low.fullLocationString + ":\n" +
                s"@local annotations on member do not match"
                reporter.error(member.pos, fullmsg)
              }
            }

            val opc = new overridingPairs.Cursor(tree.symbol)
            while (opc.hasNext) {
              if (!opc.high.isClass) checkOverride(opc.currentPair)
              opc.next()
            }

            // now check body (TODO: 2? 1?)
            body.foreach(s => traverse(s,SndMode,boundary))
        }

      case ModuleDef(mods, name, impl) =>
        traverse(impl,FstMode,boundary)

      case PackageDef(pid, stats) =>
        atOwner(tree.symbol) {
          stats.foreach(s => traverse(s,SndMode,boundary))
        }

      case _ =>
        println(s"don't know how to handle ${tree.getClass}")
    }}


    override def transform(tree: Tree): Tree = {
      traverse(tree,FstMode,Nil)
      tree
    }
  }


  class EscTransformer0(unit: CompilationUnit) extends TypingTransformer(unit) {

/* ################## TODO ##################
    Currently all info is directly obtained
    by traversing trees. This has exponential
    cost! So we really want to compute all
    information only once and store by symbol.
   ################## TODO ################## */

    def dominates(a: Symbol, b: Symbol) = 
      b.owner.owner.hasTransOwner(a.owner)
    def dominates(a: Symbol, bs: Set[Symbol]) = 
      bs.forall(_.owner.owner.hasTransOwner(a.owner))

    def checkFunResultLeak(tree: Tree, safe: Set[Symbol]): Unit = tree match {
      // TODO: handle TypeApply and other cases
      case Ident(x) =>
        val safeRes = safeArgAnn(tree.tpe.resultType)
        val unsafe = safe diff safeRes
        for (u <- unsafe) {
          // TODO: is this general enough?
          val ok = (isFunctionType(tree.tpe) && (u == tree.symbol)) ||
                   (dominates(tree.symbol, u))

          if (isFunctionType(tree.tpe) && (u == tree.symbol)) {
            reporter.warning(tree.pos, s"Note: we assume that ${tree.symbol} does not return itself.")
          }

          if (!ok) reporter.error(tree.pos, u + s" not safe (not declared as such by return type of $tree = ${tree.tpe}!")
        }

      case Select(qual@Ident(x), name) =>
        if (tree.symbol.isConstructor)
          return // TODO: ignored for now

        val safeRes = safeArgAnn(tree.tpe.resultType)
        val unsafe = safe diff safeRes
        for (u <- unsafe) {
          // TODO: is this general enough? probably not...
          val ok = isFunctionType(qual.tpe) && (u == qual.symbol)

          if (!ok) reporter.error(tree.pos, u + s" not safe (not declared as such by return type of $tree!")
        }
      case _ =>
        if (tree.symbol.isConstructor) return // TODO
        val safeRes = safeArgAnn(tree.tpe.resultType)
        val unsafe = safe diff safeRes
        if (unsafe.nonEmpty) {
          reporter.error(tree.pos, unsafe + s" not safe (not declared as such by return type of xxx $tree!")
        }
    }

    def checkFunResultAlias(tree: Tree, safe: Set[Symbol]): Unit = 
      checkFunResultLeak(tree, safe)

    // check that `safe` is never used by evaluating `tree` (free-in-expression, but transitive)
    def checkUsed(tree: Tree, safe: Set[Symbol]): Unit = tree match {
      case Literal(_) => //ok
      case Ident(x) =>
        if (safe contains tree.symbol)
          reporter.error(tree.pos, tree.symbol + " not safe (free in lambda)!")
        else if (safe.nonEmpty)
          reporter.warning(tree.pos, s"checkUsed: couldn't prove that ${tree.symbol} does not point to ${safe}")

      case ValDef(mods, name, tpt, rhs) =>
        checkUsed(rhs, safe)

      case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        checkUsed(rhs, safe)

      case Function(vparams, body) =>
        checkUsed(body, safe)

      case Select(qual, name) =>
        checkUsed(qual, safe)

      case Apply(fun, args) =>
        checkUsed(fun, safe)
        args foreach (checkUsed(_, safe))
        // TODO: what about function result?

      case Block(stats, expr) =>
        // TODO: check outside or inside lambda!
        for (s <- stats)
          checkUsed(s, safe)
        checkUsed(expr, safe)

      case New(tpt) =>
        checkUsed(tpt, safe)

      case TypeTree() => // nothing
      case _ => 
        reporter.error(tree.pos, s"not handled in checkUsed: ${tree.getClass}")
    }

    // check that the result of evaluating `tree` does not point to `safe`
    def checkAlias(tree: Tree, safe: Set[Symbol]): Unit = tree match {
      case Literal(_) => //ok
      case Ident(_) => 
        if (safe contains tree.symbol)
          reporter.error(tree.pos, tree.symbol + " not safe (checkAlias)!")
        else if (dominates(tree.symbol, safe))
          () // ok
        else if (tree.symbol.isValueParameter)
          () // ok
        else if (safe.nonEmpty)
          reporter.warning(tree.pos, s"checkAlias: couldn't prove that ${tree.symbol} does not point to ${safe}")

      case Function(vparams, body) =>
        // closure conversion: closure points to all its free variables, plus transitive
        // so, none of the free variables may point to `save`
        checkUsed(body, safe)

      case Select(qual, name) =>
        // TODO: what's the right thing for select?
        checkAlias(qual, safe)

      case Apply(fun, args) =>
        // the object returned from a function call may not point to `save`

        //reporter.error(tree.pos, s"not handled in findSep: ${tree.getClass}")

        if (fun.symbol.isConstructor && args.isEmpty)
          return

        // TODO: fun arg?
        val safeRes = safeArgAnn(fun.tpe.resultType)
        val unsafe = safe diff safeRes
        if (unsafe.nonEmpty)
          reporter.error(tree.pos, s"couldn't prove that object returned from ${tree} does not point to $unsafe")

      case Block(stats, expr) =>
        // object computed by result expression may not point to `save`
        checkAlias(expr, safe)

      case This(qual) => // TODO: ok?

      case TypeTree() => // TODO: what?

      case Throw(expr) => // ok

      case Match(selector, cases) =>        
        cases foreach { case cd @ CaseDef(pat, guard, body) =>
          checkAlias(body, safe)
        }

      case _ => 
        reporter.error(tree.pos, s"not handled in checkAlias: ${tree.getClass}")
    }

    // check that the result of evaluating `tree` does not point to `safe`
    def checkDeepOnlyAlias(tree: Tree, safe: Set[Symbol]): Unit = tree match {
      case Literal(_) => //ok
      case Function(vparams, body) =>
        // closure conversion: closure points to all its free variables, plus transitive
        // so, none of the free variables may point to `save`
        checkAlias(body, safe)

      case Apply(fun, args) =>
        // the object returned from a function call may not point to `save`
        //reporter.error(tree.pos, s"not handled in findSep: ${tree.getClass}")
        if (fun.symbol.isConstructor && args.isEmpty)
          return

        reporter.error(tree.pos, s"couldn't prove that object returned from ${tree} does not point to $safe")

      case Block(stats, expr) =>
        // object computed by result expression may not point to `save`
        checkDeepOnlyAlias(expr, safe)

      case _ => 
        reporter.error(tree.pos, s"not handled in checkAlias: ${tree.getClass}")
    }

    // check that evaluating `tree` does not leak `safe` (main entrypoint)
    def checkLeak(tree: Tree, safe: Set[Symbol]): Unit = tree match {
      case Literal(_) => // ok
      case Ident(x) => // ok
      case Apply(fun, Nil) =>
        checkLeak(fun, safe)
        checkFunResultLeak(fun, safe)
      case Apply(fun, arg::Nil) => // TODO: multi-arg
        // (1) check safe in the expression that computes the function
        checkLeak(fun, safe)

        val safeRes = safeArgAnn(fun.tpe.resultType)
        val argEscapes = 
             (!safeRes.contains(fun.tpe.params.head) && 
              !safeRes.exists(isPercentMarker)) 
              // FIXME: check that this matches function arg!

        // (2) check safe in the expression that computes the argument
        checkLeak(arg, safe)
        
        dprintln("* apply " + tree)
        dprintln("  safeRes: "+safeRes + " of " + fun.tpe)
        if (argEscapes) {

          // (3.1) if fun leaks its arg, need to check that arg *object* may not reference `safe`
          checkAlias(arg, safe)
        } else {

          // (3.2): if fun doesn't leak its arg, we need to check more.
          // No operation whatsoever on `arg` may ever extract `safe`.
          checkDeepOnlyAlias(arg, safe)
        }

        // (4) check safe in the function result (when executing the function)
        checkFunResultLeak(fun, safe)

      case ValDef(mods, name, tpt, rhs) =>
        checkLeak(rhs, safe)

      case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        // nothing to do

      case TypeApply(fun, args) =>
        checkLeak(fun, safe)
        for (arg <- args) checkLeak(arg, safe)
        // TODO: enough? or need to look at result type?

      case Select(qual, name) =>
        checkLeak(qual, safe)

      case Function(vparams, body) =>
        // function is a value --> no evaluation, so nothing happens
        //findSafe(body, true, safe) // TODO

      case Block(stats, expr) =>
        for (s <- stats)
          checkLeak(s, safe)
        checkLeak(expr, safe)

      case New(tpt) =>
        checkLeak(tpt, safe)

      case This(qual) => // TODO: ok?

      case TypeTree() => // TODO: what?

      case Throw(expr) => 
        checkLeak(expr, safe)

      case Match(selector, cases) =>        
        checkLeak(selector, safe)
        cases foreach { case cd @ CaseDef(pat, guard, body) =>
          checkLeak(body, safe)
        }

      case _ => 
        reporter.error(tree.pos, s"not handled in checkLeak: ${tree.getClass}")
    }


    // currently not used...
    def findUsed(tree: Tree): Set[Symbol] = tree match {
      case Literal(_) => 
        Set() //ok
      case Ident(x) =>
        Set(tree.symbol)
      case Apply(fun, args) =>
        (fun::args) map findUsed reduceLeft (_ union _)
      case TypeApply(fun, args) =>
        (fun::args) map findUsed reduceLeft (_ union _)
      case TypeTree() => // TODO: what?
        Set()
      case Select(qual, name) =>
        findUsed(qual)
      case Function(vparams, body) =>
        findUsed(body) diff (vparams map (_.symbol) toSet)
      case Block(stats, expr) =>
        (stats:+expr) map findUsed reduceLeft (_ union _)
      case New(tpt) =>
        Set() // TODO
      case _ => 
        reporter.error(tree.pos, s"not handled in findUsed: ${tree.getClass}")
        Set()
    }

    // currently not used...
    def findShared(tree: Tree): Set[Symbol] = tree match {
      case Literal(_) => 
        Set() //ok
      case Ident(x) =>
        Set(tree.symbol) // get transitive!!
      case Apply(fun, args) =>
        (fun::args) map findUsed reduceLeft (_ union _)
      case TypeApply(fun, args) =>
        (fun::args) map findUsed reduceLeft (_ union _)
      case TypeTree() => // TODO: what?
        Set()
      case Select(qual, name) =>
        findUsed(qual)
      case Function(vparams, body) =>
        findUsed(body) diff (vparams map (_.symbol) toSet)
      case Block(stats, expr) =>
        (stats:+expr) map findUsed reduceLeft (_ union _)
      case New(tpt) =>
        Set() // TODO
      case _ => 
        reporter.error(tree.pos, s"not handled in findShared: ${tree.getClass}")
        Set()
    }

    def checkAllInit(tree: Tree, safe: Set[Symbol]) = if (safe.nonEmpty) {
      dprintln(s"++ checkLeak $safe")
      checkLeak(tree,safe)
      dprintln(s"++ checkAlias $safe")
      checkAlias(tree, safe)
    }

    override def transform(tree: Tree): Tree = tree match {
      case DefDef(mods, name, tparams, vparamss, tpt, rhs) if !tree.symbol.isConstructor =>
        dprintln("--- recurse def: ${tree.symbol}")
        val res = super.transform(tree)
        val args = vparamss flatMap (_ map (_.symbol)) toSet;
        val ann = safeArgAnn(tpt.tpe.resultType)
        val ann1 = if (ann exists isPercentMarker)
          ((ann filterNot isPercentMarker) ++ args) else ann
        checkAllInit(rhs, ann1)
        res
      case Function(vparams, body) =>
        dprintln(s"--- recurse func: ${tree.tpe}")
        val res = super.transform(tree)
        val args = vparams.map(_.symbol).toSet
        if (!isFunctionType(tree.tpe)) {
          reporter.error(tree.pos, "function type expected")
        } else {
          val ann = safeArgAnn(tree.tpe.widen.typeArgs.last)
          val ann1 = if (ann exists isPercentMarker)
            ((ann filterNot isPercentMarker) ++ args) else ann            
          checkAllInit(body, ann1)
        }
        res
      case _ =>
        super.transform(tree)
    }
  }

}
