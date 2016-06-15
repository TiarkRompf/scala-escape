package scala.tools.escape

import org.junit.Test
import org.junit.Assert.assertEquals

import scala.annotation._
import scala.collection.Seq
import scala.collection.generic.CanBuildFrom
import scala.language.{ implicitConversions, higherKinds }
import scala.util.escape._
import scala.util.control.Exception

class Basic extends CompilerTesting {
  @Test def test10 = {
    val x = 100
    val y = 99

    def f(a:Int): Int @safe(x) = a

    def g1(a:Int): Int @safe(x) = f(a)

    def g(a:Int): Int @safe(x) = a

    def h(a: Int): Int @safe(x) = g(f(a))
  }

  @Test def test20 = expectEscErrorOutput(
    /*  Why we don't have this error right now?
        Did we get errors before?
    "value x not safe (not declared as such by return type of f = (a: Int)Int!\n"+
    "couldn't prove that object returned from f(a) does not point to Set(value x)",
    */
    "",
  """
    val x = 100
    val y = 99

    def f(a:Int): Int = a
    def g(a:Int): Int @safe(x) = f(a) // not safe
  """)

  @Test def test30 = {
    val x = 100
    val y = 99

    def f(a:Int): Int = a
    def g(a:Int): Int @safe(x) = f(a) // not safe
  }

  @Test def trycatch4 = expectEscErrorOutput(
    /*  Why we don't have this error right now?
        Did we get errors before?
    "value raise not safe (free in lambda)!",
    */
    "",
    """

    def trycatch(f: (Exception => Nothing) => Int @safe(%)): Int = ???

    def safeMethod(f: () => Int): Int @ safe(f) = ???
    def unsafeMethod(f: () => Int): Int = ???

    trycatch { raise =>

      safeMethod { () =>
        raise(new Exception)  // ok
        7
      }

      unsafeMethod { () =>
        raise(new Exception)  // not ok
        7
      }
      7
    }
  """)
}


class Local extends CompilerTesting {
  @Test def test10: Unit = {
    class IO
    def println(s:String)(@local io: IO) = Console.println(s)

    def foo(f: Int->Int) = f(1)

    def g(@local x: Int) = 2 // return x should fail

    foo(x => 2*g(x))
  }
  /**
    * [error] /Users/AllenWu/Code/scala-escape/library/src/test/scala/scala/tools/escape/TestSuite.scala:99: value io cannot be used inside method foo
    * [error]     def foo = println("foo")(io)  // fails
    */
  @Test def test11: Unit = {
    // expectEscError("value io cannot be used inside method foo", """
    class IO
    def println(s:String)(@local io: IO) = Console.println(s)

    @local val io = new IO

//    def foo = println("foo")(io)  // fails

    @local def bar = println("bar")(io)  // ok
      // """)
  }
  /**
    * [error] /Users/AllenWu/Code/scala-escape/library/src/test/scala/scala/tools/escape/TestSuite.scala:110: value io cannot be used inside value $anonfun
    * [error]     val foo = () => println("foo")  // fails
    */
  @Test def test12: Unit = {
    // expectEscErrorOutput("value io cannot be used inside value $anonfun", """
    class IO
    def println(s:String)(implicit @local io: IO) = Console.println(s)

    implicit @local val io = new IO

//    val foo = () => println("foo")  // fails

    @local val bar = () => println("bar")  // ok

    def handler(@local f: Int => Int) = f(7)

    handler { x => bar(); 2 }
      // """)
  }
  /**
    * [error] /Users/AllenWu/Code/scala-escape/library/src/test/scala/scala/tools/escape/TestSuite.scala:126: overriding method foo in class A with method foo in class B:
    * [error] some @local annotations on arguments have been dropped
    * [error]       def foo(x: Int): Int = x
    */
  @Test def test13: Unit = {

    abstract class A {
      def foo(@local x: Int): Int
    }
/*
    class B extends A {
      def foo(x: Int): Int = x
    }

    @local val y = 8

    val b: A = new B
    b.foo(y)
*/
  }

  @Test def test14: Unit = {

    val f = new java.io.File("foo")
    val s = ESC.NO(f.getCanonicalPath())
  }

  /**
    * [error] /Users/AllenWu/Code/scala-escape/library/src/test/scala/scala/tools/escape/TestSuite.scala:174: method println cannot be used inside value $anonfun
    * [error]     xs.foreach(x => println(x)) // error
    * [error]
    */
  @Test def test15: Unit = {

    trait MySeq[A] {

      type LT
      type plocal = local[LT]

      def foreach(@plocal f: A => Unit): Unit

      def map[B](@plocal f: A => B) = {
        var b: B = null.asInstanceOf[B]
        foreach { x => b = f(x) }
        b
      }

    }

    trait MyList[A] extends MySeq[A] {
      type LT = Any
      def foreach(@local f: A => Unit): Unit = { }
    }

    trait MyStream[A] extends MySeq[A] {
      type LT = Nothing
      def foreach(f: A => Unit): Unit = { }
    }

    @local def println(x: Any): Unit = ()

    val xl = new MyList[Int] {}
    val xs = new MyStream[Int] {}

    xl.foreach(x => println(x)) // ok
//    xs.foreach(x => println(x)) // error
  }

/*
  @Test def test20 = expectEscErrorOutput(
    "value x not safe (not declared as such by return type of f = (a: Int)Int!\n"+
    "couldn't prove that object returned from f(a) does not point to Set(value x)",
  """
    val x = 100
    val y = 99

    def f(a:Int): Int = a
    def g(a:Int): Int @safe(x) = f(a) // not safe
  """)
*/
}




class TryCatch extends CompilerTesting {

  @Test def trycatch1: Unit = { () =>

    def trycatch(f: (Exception => Nothing) => Unit @safe(%)): Unit = ???

    trycatch { raise =>
      raise(new Exception)
    }

  }

  @Test def trycatch2: Unit = { () =>

    def trycatch(f: (Exception => Nothing) => Unit @safe(%)): Unit = ???

    def safeMethod(f: () => Unit): Unit @ safe(f) = ???

    trycatch { raise =>
      safeMethod { () =>
        raise(new Exception)  // ok
        ()
      }
      ()
    }

  }

  @Test def trycatch3: Unit = { () =>

    def trycatch(f: (Exception => Nothing) => Int @safe(%)): Int = ???

    def safeMethod(f: () => Int): Int @ safe(f) = ???

    trycatch { raise =>

      def inner(a:Int): Int @safe(raise) = a

      safeMethod { () =>
        raise(new Exception)  // ok
        inner(7)
      }

      9
    }

  }



  @Test def trycatch4: Unit = try {
    // expectEscErrorOutput("value raise not safe (free in lambda)!","""

    def trycatch(f: (Exception => Nothing) => Int @safe(%)): Int = ???

    def safeMethod(f: () => Int): Int @ safe(f) = ???
    def unsafeMethod(f: () => Int): Int = ???

    trycatch { raise =>

      safeMethod { () =>
        raise(new Exception)  // ok
        7
      }

      unsafeMethod { () =>
        raise(new Exception)  // not ok
        7
      }
      7
    }
  } catch { case e: scala.NotImplementedError => }

  @Test def trycatch5 = expectEscErrorOutput(
    /* FIXME */ // "couldn't prove that object returned from inner(7) does not point to Set(value raise)","""
    "", """
    def trycatch(f: (Exception => Nothing) => Int @safe(%)): Int = ???

    def safeMethod(f: () => Int): Int @ safe(f) = ???

    trycatch { raise =>

      def inner(a:Int): Int = a

      safeMethod { () =>
        raise(new Exception)  // ok
        inner(7) // not ok
      }

      7
    }
  """)

}
