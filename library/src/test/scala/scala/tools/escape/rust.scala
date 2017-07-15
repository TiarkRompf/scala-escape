package scala.tools.escape
package rust

import org.junit.{ Ignore, Test }
import org.junit.Assert.assertEquals

import scala.annotation._
import scala.language.{ implicitConversions, higherKinds }
import scala.util.escape._

import shapeless._, shapeless.test.{illTyped,sameTyped,showType,typed}
import syntax.singleton._ // for narrow
import tag.@@

object MutSamePrivilegeAndUnrelated {

  class Mut[T]
  class Imm[-T] // [S, -T <: S]() // extends Mut[S]()

  class LowPriorityMutability
  object LowPriorityMutability {
    implicit def vToMut[T](v: T): Var[T, Mut[T]] = new Var[T, Mut[T]](v)
  }

  object Var {
    implicit def vToImm[T](v: T): Var[T, Imm[T]] = new Var[T, Imm[T]](v)
  }
  class Var[T, A/*: Aliased*/](private var v: T)
  // (implicit ev: Aliased[A]
      extends LowPriorityMutability {
    def value = v
    def value_=(v2: T)(implicit ev: A =:= Mut[T]) // allow only for mutable
    { v = v2 }
  }

  def bindImm[T, U](@local ref: Var[T, Imm[T]])(
    @local fn: Var[T, Imm[T]] -> U) = fn(new Var[T, Imm[T]](ref.value))

  // def bindMut[T, U](v: T)(
  def bindMut[T, U](v: Var[T, Mut[T]])(@local fn: Var[T, Mut[T]] -> U) =
    fn(v)
  // {
  //   //   import Aliased._
  //   // implicit val ev = new MutWitness[T](v)
  //   implicit val vWitness = v
  //   val vEv = implicitly[Mut[T]]
  //   // val ev = implicitly[MutWitness[T]]
  //   fn(new Var[T, Mut[T]](v)// (new MutWitness[T](v))
  //   )
  // }

  // STATIC TEST

  // // TODO(lo) why this doesn't work?
  // illTyped { """
  //     bindImm(1) { one =>
  //       one.value = 2
  //     }
  // """ }

  bindImm(1) { one =>
    // one.value = 2 // error (setter not enabled for immutable)
  }

  bindMut(42) { mut =>
    mut.value = 21

    // bindMut(mut) { mutSame => } // error (mut is not 1st-class)
    // val mutSame = mut // error (mut is not 1st-class)
    bindMut(42) { mut42 => } // ok (another instance initialized to same value)

    // bindImm(mut) { imm => } // error (mut is not 1st-class ref nor a value)
    bindImm("value") { imm => // ok
      // bindMut(imm) { mutOfImm => } // error (imm is not 1st-class)
      bindImm(imm) { imm2 => } // ok (imm is 2nd-class)
    }
  }

  // IGNORE BELOW (other failed attempts)

  // type classes
  class Aliased[T]
  object Aliased {
    // implicit object MutWitness extends Aliased[Mut[_]]
    // implicit object ImmWitness extends Aliased[Imm[_]]
    implicit class MutWitness[T](mut: Mut[T]) extends Aliased[Mut[T]]
    implicit class ImmWitness[T](t: T) extends Aliased[Imm[T]]
    // implicit def showMut[T](implicit t: T): Aliased[Mut[T]] = new MutWitness[T](t)
  }

  // TODO(md) should we NOT allow mutable variables?
  // def bindImm[T, U, A: Aliased](@local ref: Var[T, A])(
  //   @local fn: Var[T, A/*Imm[T, T]*/] -> U) = {
  //   @local val vr = new Var[T, A](ref.value)
  //   fn(vr)
  // }

  // def bindImm[T, U](v: T)(@local fn: `->`[Var[T, Imm[T, T]], U]) =
  //   fn(new Var[T, Imm[T, T]](v))
  // def bindImm[T, U](ref: Var[T, Mut[T]])(
  //   @local fn: Var[T, Mut[T]] -> U) = fn(
  //   ref.value // new Var[T, Mut[T]](ref.value)
  // )

  // // def bindMut[T, U](v: T)(
  // def bindMut[T, U](v: Var[T, Mut[T]])(
  //   @local fn: Var[T, Mut[T]] -> U) = {
  //   import Aliased._
  //   // implicit val ev = new MutWitness[T](v)
  //   implicit val vWitness = v
  //   val vEv = implicitly[Mut[T]]
  //   // val ev = implicitly[MutWitness[T]]
  //   fn(new Var[T, Mut[T]](v)// (new MutWitness[T](v))
  //   )
  // }

  bindMut(0) { m =>
    // @local val i = (mut: Mut[Imm[Int, Int]]) // TODO(hi) symbol value <error>
    // bindImm(mut) { mut =>
    //   mut.value = 2
    //   imm.value = 34
    //   val imm2: Imm[Any, Int] = imm
    // }
  }
}

class MutSamePrivilegeAndUnrelated extends CompilerTesting {
  // @Test def testCannotReassignImmutable = expectEscErrorOutput(
  //   "",
  //   """
  //   bindImm(1) { one =>
  //     one.value = 2
  //   }
  //   """)
}

class MutHigherPrivileged extends CompilerTesting {

  // Refresher: `->*`[P, T, U] desugars to: (@local[P] T) => U

  type Mut = Any // Mutable binding
  trait Imm // Immutable binding, must be less-privileged (more permissive)

  // Observations:
  // - v cannot be @local[Mut] (required), but can be 1st-class (will coerce)
  def bind[T, U](@local[Imm] v: T)(@local[Imm] fn: `->*`[Imm, T, U]): U = fn(v)

  def bindMut[T, U](v: T)(fn: `->*`[Mut, T, U]): U = fn(v)

  { // static test (OK)

    {
      val outer = 42
      val ret = bind(outer) { outerRef =>
        @local[Imm] val inner = outerRef    // ok
        @local[Mut] val innerMut = outerRef // undesirable!
        bind(outer) { outerRef2 => () }
        42
      }
    }

    {
      val outer = 42
      val ret = bind(outer) { outerRef =>
        // val inner = outerRef; // error: outerRef cannot be used as 1st-class
        bind(outer) { outerRef2 => () }
        42
      }
    }
    {
      val outer = 42
      val ret = bind(outer) { outerRef =>
        val inner = outerRef; // BUG: no error (but outerRef is contravariant)
        42
      }
    }
  }

  class Var[T](v: T) {
    type A >: Imm
  }

  class ImmVar[T](v: T) extends Var(v) {
    type A >: Mut
  }

  @Test def testImmutable = expectEscErrorOutput(
    "",
    """
    """)
}

class MutSubtypePathDep {
  trait Imm
  trait Mut extends Imm
  // type Imm = Any
  // type Mut = Nothing

  // trait Mut
  // trait Imm extends Mut

  // class Val[T](val value: T) {
  //   type A >: Mut
  // }

  // class Val[T](val value: T) {
  //   type
  // }

  // class Val[T](val value: T) {
  //   type A <: Imm
  // }

  // class Var[T](v: T) extends Val(v) {
  class Var[T](val value: T) {
    type A >: Mut
    // def update(idx: Int, val
  }

  def bindMut[T, U](v: Var[T])(
    @local body: v.A -> U) = body(new Mut {})
  def bind[T, U](v: Var[T] { type A >: Imm })(
    @local body: v.A -> U) = body(new Imm {})

  implicit def toImm[T](v: Var[T]) = new Var[T](v.value) { type A >: Imm }

  { // static test
    val mr = new Var[Int](1)
    bind(mr) { imm =>
      bind(mr) { imm =>
      }
    }

    bindMut(mr) { mut =>
      bind(mr) { imm =>
      }
    }
  }
}

class ValVsVarWrapper {
  trait Mut[+A] // FIXME: -> A
  trait Imm[+A] extends Mut[A]

  class Val[T](val value: T) {
    type A >: Imm[T]
  }

  class Var[T](v: T) extends Val(v) {
    type A >: Any
  }

  object Var {
    def apply[T](v: T): Var[T] = Var[T](v)
  }

  def bindMut[T, L >: Mut[Any], U](@local[Imm[T]] v: Var[T])(
    // @local[L with v.A forSome { L >: impl.L }
    @local[L with v.A] fn: Var[T] => U) = //`->*`[Mut[T], Var[T], U]): Unit =
    fn(new Var[T](v.value) {
    })

  def staticTest = {

    {
      // @local[Imm[Int]]
      val mi = Var(1)
      @local[Mut[String]]
      val ms = new Var[String]("s")
      bindMut(mi) { mi1 =>
        @local val ms2 = ms;
        ()
      }
    }

    val mr = Var(1)
    bindMut(mr) { mr1 =>
      bindMut(mr) { mr2 =>
        ()
      }
      ()
    }
  }
}

class AliasTagTest extends CompilerTesting {

  type Tagged[U] = { type Tag = U }
  type @@[+T, U] = T with Tagged[U] // TODO(Tiark) what difference does +T make?

  class Tagger[U] {
    def apply[T](t : T) : T @@ U = t.asInstanceOf[T @@ U]
  }

  def tag[U] = new Tagger[U]

  trait M
  trait I extends M

  class Imm[+T](value: T) { // must be +T (also consistent with Rust)
    type A >: I
  }

  class Mut[T](value: T) extends Imm[T](value) { // must be T (invariant)
    type A >: M
  }

  // approx. usage:
  // bind(x1) { implicit imm_x: Imm[T] =>
  //   bind(x2) { implicit imm_x: x =>
  //     ...
  //   }
  // }

  def bind[T](value: T)(fn: Imm[T] => Unit)(implicit b: Imm[T]) = { }

  // note: attempting to "cheat" by introducing supertype of Mut, i.e.:
  //   bindMut(x) { implicit x_mut: Imm => { ... }" causes
  // will cause ambiguous implicit ^^ (provided not intentionally shadowed),
  // since if there is an immutable binding for the same variable, x_imm,
  // neither is more specific (both have type
  def bindMut[T](value: T)(fn: Mut[T] => Unit) = { }

  // approx. usage:
  // bindMut(x) { implicit mut_x: Imm[...] =>
  //   bindMut(y) { implicit mut_x: Imm[23] =>
  //   }
  // }

  val immStr: Imm[AnyRef] = new Imm[String]("abc") // ok
  // val immDowncast: Imm[String] = new Imm[AnyRef](null) // error

  class My
  val mutMy: Mut[My] = new Mut[My](new My)
  // val mutUpcast: Mut[Any] = new Mut[My](new My) // error

  // IGNORE BELOW

  // implicit def toMut[T](value: T) = new Mut[T] { type A = T }
}
