package scala.tools.escape

import org.junit.{ Ignore, Test }
import org.junit.Assert.assertEquals

import scala.annotation._
import scala.language.implicitConversions

import shapeless._, shapeless.test.{illTyped,sameTyped,showType,typed}

object HListTest {
  def isDistinct[L <: HList](l: L)(implicit ev: IsDistinctConstraint[L]) = true

  implicit val ctx: HNil = HNil // need type ascription (otherwise singleton)

  // {
  //   def bind[H, T <: HList, U](v: H)(body: (H :: T) => U) = ???
  // }

  import syntax.singleton._ // for narrow

  val outerStr = "foo"
  val outerStrN = outerStr.narrow
  val outerStr2 = "bar"
  val outerInt = 42

  import tag.@@

  {
    abstract class Imm[V](value: V) {
      type C
      val ctx: C
    }

    object Imm {
      type Aux[V, C0 <: HList] = Imm[V] { type C = V :: C0 }
      def apply[V, T <: HList](v: V)(implicit c: T) = new Imm[V](v) {
        type C = V :: T
        val ctx = v :: c
      }
    }

    def bind[V, L <: HList](
      v: V
    )(
      body: Imm.Aux[V, L] => Unit
    )(implicit ctx: L) = Imm(v)

    // bind(1) { i: Imm[Int] => implicit ctx => // ???
    bind(1) { i: Imm[Int] => implicit ctx: String :: HNil => // ???
      implicitly[String :: HNil]
      ()
    }
    // bind { abc: String => ctx: HNil =>
    //   ()
    // }
  }

  {
    implicit
    class Imm[+V, L <: HList // must be +V (also consistent with Rust)
    ](val v: V)  (implicit val ctx: L)
    { self =>
      val vWitness = Witness(v)
      type A = vWitness.T //>: V  // if -V
      def value: A = vWitness.value //v

      // type C
      type C = L
      // def bind0[U](body: A => U) = ???
      // (implicit ctx: T) = ???
    }

    // object Imm {
    //   type Aux[A0, L <: HList] = Imm[A0, L] { type A = A0; type C = L }
    // }

    // implicit def toImm[V, L <: HList](v: V)(implicit ctx: L) = //: Imm.Aux[V, L] =
    //   new Imm(v) { type A = V; type C = L }

    class Mut[V <: Singleton, L <: HList // must be V (also consistent with Rust)
    ](v0: V)(                 // TODO: does class parameter makes sense?
      implicit val ctx: L
    ) { self =>
      private[this] var v: V = v0
      // val wThis = Witness(this) // TODO: error, this not stable (nor is self)
      // type A = wThis.T
      def value: V = v0
      def set(v: V) = this.v = v
      type C
    }
    implicit def toMut[V <: Singleton, L <: HList](v: V)(implicit ctx: L) = //: Imm.Aux[V, L] =
      new Mut(v) { type C = V :: L }

    // { // basic test
    //   val m = new Mut("foo".narrow)
    //   m.set(42)
    // }
    {
      import syntax.singleton._
      val m = new Mut("foo".narrow)
      illTyped(""" m.set(42) """)
    }

    trait I // tag type for immutable
    trait M // tag type for mutable

    def bind[H, T <: HList, U](v: Imm[H, T]) //(ctx: T) // ctx moved into Imm
      (body: (v.A @@ I) :: T => U) = body(tag[I](v.value) :: v.ctx)

    def bindMut[H, T <: HList, U](v: Imm[H, T])
      (body: (H @@ M) :: T => U) = body(tag[M](v.value) :: v.ctx)

    def isPure[L <: HList](ctx: L)(implicit ev: LUBConstraint[L, Any @@ I]) =
      ctx

    bind(outerStr) //(ctx)
    { implicit ctx => //: Imm[String] :: HNil =>
      implicitly[String :: HNil]
      implicitly[(String @@ I) :: HNil]
      isDistinct(ctx)
      typed[String :: HNil](ctx)

      bind(outerInt)//(ctx)
      { implicit ctx => // FIXME: typo in ctx causes error in inner bind scope
        isDistinct(ctx)
        typed[Int :: String :: HNil](ctx)
        typed[Int :: String :: HNil](ctx)
        isPure(ctx)

        bind(outerStr)//(ctx)
        { implicit ctx =>
          // illTyped("""
            isDistinct(ctx)
          // """)
        }

        // bind(outerStr2) { implicit ctx =>
        //   isDistinct(ctx)
        // }
      }

      bindMut(outerInt) { implicit ctx =>
        illTyped("""
          isPure(ctx)
        """)
      }
    }
    // outer.bind { ctx2 =>
    //   ()
    // }
  }
}
