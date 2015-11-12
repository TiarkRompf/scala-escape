package scala.tools.escape

import scala.tools.nsc.{ Global, Mode }
import scala.tools.nsc.MissingRequirementError

import scala.language.postfixOps

abstract class EscAnnotationChecker extends EscUtils {
  val global: Global
  import global._
  import analyzer.{AnalyzerPlugin, Typer}
  import definitions._

  /**
   *  Checks whether @safe annotations conform
   */
  object checker extends AnnotationChecker {

    /** Check annotations to decide whether tpe1 <:< tpe2 */
    def annotationsConform(tpe1: Type, tpe2: Type): Boolean = {
      vprintln("check annotations: " + tpe1 + " <:< " + tpe2)

      // Nothing is least element, but Any is not the greatest

      // FIMXE: NOT FOR @safe
      if (tpe1.typeSymbol eq NothingClass)
        return true


/*
      val annL1 = hasLocalMarker(tpe1)
      val annL2 = hasLocalMarker(tpe2)

      if (annL1 || annL2)
        vprintln("check safe: " + tpe1.withoutAnnotations + " " + annL1 + " <:< " + tpe2.withoutAnnotations + " " + annL2)

      if (annL1 && !annL2) // A <: A @local but not A @local <: A
        return false

      if (annL1 && annL2)
        return true // premature?
*/

      // ----


      val annS1 = safeArgAnn(tpe1)
      val annS2 = safeArgAnn(tpe2)

      if (annS1.nonEmpty || annS2.nonEmpty)
        vprintln("check safe: " + tpe1.withoutAnnotations + " " + annS1 + " <:< " + tpe2.withoutAnnotations + " " + annS2)

      if (!annS2.forall(annS1)) // slightly redundant, but let's make our intention precise ...
        return false

      if (annS1 == annS2)
        return true

      // Need to handle uninstantiated type vars specially:

      // g map (x => x)  with expected type List[Int] @cps
      // results in comparison ?That <:< List[Int] @cps

      // Instantiating ?That to an annotated type would fail during
      // transformation.

      // Instead we force-compare tpe1 <:< tpe2.withoutAnnotations
      // to trigger instantiation of the TypeVar to the base type

      // This is a bit unorthodox (we're only supposed to look at
      // annotations here) but seems to work.

      if (!annS2.isEmpty && !tpe1.isGround)
        return tpe1 <:< tpe2.withoutAnnotations

      false
    }

/*
    /** Refine the computed least upper bound of a list of types.
     *  All this should do is add annotations. */
    override def annotationsLub(tpe: Type, ts: List[Type]): Type = {
      if (!cpsEnabled) return tpe

      val annots1 = cpsParamAnnotation(tpe)
      val annots2 = ts flatMap cpsParamAnnotation

      if (annots2.nonEmpty) {
        val cpsLub = newMarker(global.lub(annots1:::annots2 map (_.atp)))
        val tpe1 = if (annots1.nonEmpty) removeAttribs(tpe, MarkerCPSTypes) else tpe
        tpe1.withAnnotation(cpsLub)
      }
      else tpe
    }
*/

    /** Refine the bounds on type parameters to the given type arguments. */
    override def adaptBoundsToAnnotations(bounds: List[TypeBounds], tparams: List[Symbol], targs: List[Type]): List[TypeBounds] = {
      val anySafe = filterAttribs(targs.last, MarkerSafe)
      if (isFunctionType(tparams.head.owner.tpe_*) || isPartialFunctionType(tparams.head.owner.tpe_*)) {
        vprintln("function bound: " + tparams.head.owner.tpe + "/"+bounds+"/"+targs)
        if (hasSafeMarker(targs.last))
          bounds.reverse match {
            case res::b if !hasSafeMarker(res.hi) =>
              (TypeBounds(res.lo, res.hi.withAnnotations(anySafe))::b).reverse
            case _ => bounds
          }
        else
          bounds
      }
      else if (tparams.head.owner == ByNameParamClass) {
        vprintln("byname bound: " + tparams.head.owner.tpe + "/"+bounds+"/"+targs)
        val TypeBounds(lo, hi) = bounds.head
        if (hasSafeMarker(targs.head) && !hasSafeMarker(hi))
          TypeBounds(lo, hi withAnnotations anySafe) :: Nil
        else bounds
      } else
        bounds
    }

  }

  object plugin extends AnalyzerPlugin {

    import checker._

    override def canAdaptAnnotations(tree: Tree, typer: Typer, mode: Mode, pt: Type): Boolean = {
      vprintln("can adapt annotations? " + tree + " / " + tree.tpe + " / " + mode + " / " + pt)

      val annL1 = safeArgAnn(tree.tpe)
      val annL2 = safeArgAnn(pt)

      if (mode.inExprMode) {
        if (annL1 != annL2) 
          return true
        vprintln("already same, can't adapt further")
      }

      false
    }


    def setSafe(tree: Tree, xs: Set[Symbol]) = {
      val ann = AnnotationInfo(MarkerSafe.tpe, (xs map (x => gen.mkAttributedIdent(x))).toList, Nil)
      tree.modifyType(tpe => removeAttribs(tpe,MarkerSafe).withAnnotation(ann))
    }

    override def adaptAnnotations(tree: Tree, typer: Typer, mode: Mode, pt: Type): Tree = {
      vprintln("adapt annotations " + tree + " / " + tree.tpe + " / " + mode + " / " + pt)

      val annL1 = safeArgAnn(tree.tpe)
      val annL2 = safeArgAnn(pt)

      if (mode.inExprMode) {
        if (annL2 != annL1) {
          return setSafe(tree, annL2)
        }
      }

      tree
    }

    /** Modify the type that has thus far been inferred
     *  for a tree.  All this should do is add annotations. */

    override def pluginsTyped(tpe: Type, typer: Typer, tree: Tree, mode: Mode, pt: Type): Type = {
      // val report = try hasCpsParamTypes(tpe) catch { case _: MissingRequirementError => false }
      // if (report)
      //   reporter.error(tree.pos, "this code must be compiled with the Scala escape plugin enabled")

      tpe
    }
  }
}
