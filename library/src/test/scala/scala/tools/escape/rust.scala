package scala.tools.escape
package rust

import org.junit.{ Ignore, Test }
import org.junit.Assert.assertEquals

import scala.annotation._
import scala.language.{ implicitConversions, higherKinds }
import scala.util.escape._

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
