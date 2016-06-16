package scala.tools.escape

import org.junit.Test
import org.junit.Assert.assertEquals

import scala.annotation._
import scala.collection.Seq
import scala.collection.generic.CanBuildFrom
import scala.language.{ implicitConversions, higherKinds }
import scala.util.escape._
import scala.util.control.Exception

import java.io.{StringWriter,PrintWriter}

class Basic extends CompilerTesting {
  @Test def test01 = expectEscErrorOutput(
  "value x cannot be used as 1st class value @local[Nothing]",
  """    
    def fst(@local x: String) = println(x)
  """)

  @Test def test02 = expectEscErrorOutput(
  "value x cannot be used as 1st class value @local[Nothing]",
  """    
    def fst(@local x: String) = x
  """)

  @Test def test03 = expectEscErrorOutput(
  "value x cannot be used as 1st class value @local[Nothing]",
  """
    var c = "init"
    def fst(@local x: String) = { c = x }
  """)


  @Test def test10 = {
    def withFile[R](n: String)(@local fn: PrintWriter -> R): R = {
      val f = new PrintWriter(new StringWriter()); try fn(f) finally f.close()
    }
    withFile("test.out") { f => f.println("hello") }
  }

  @Test def test11 = {
    def withFile[R](n: String)(@local fn: PrintWriter -> R): R = {
      val f = new PrintWriter(new StringWriter()); try fn(f) finally f.close()
    }
    def handler(@local f: PrintWriter) = { // error without @local
      f.println("hello")
    }
    withFile("test.out") { f => handler(f) }
  }

  @Test def test12 = expectEscErrorOutput(
  "value f cannot be used as 1st class value @local[Nothing]",
  """
    import java.io.{PrintWriter,StringWriter}
    def withFile[R](n: String)(@local fn: PrintWriter -> R): R = {
      val f = new PrintWriter(new StringWriter()); try fn(f) finally f.close()
    }
    def handler(f: PrintWriter) = { // error without @local
      f.println("hello")
    }
    withFile("test.out") { f => handler(f) }
  """)


  @Test def test13 = {
    def withFile[R](n: String)(@local fn: PrintWriter -> R): R = {
      val f = new PrintWriter(new StringWriter()); try fn(f) finally f.close()
    }
    def wrapper(fn: PrintWriter -> Unit) = withFile("test.out") { f =>
      f.println("begin"); fn(f); f.println("end")
    }
    wrapper { f => f.println("yay") }
  }

  @Test def test14 = {
    def withFile[R](n: String)(@local fn: PrintWriter -> R): R = {
      val f = new PrintWriter(new StringWriter()); try fn(f) finally f.close()
    }
    withFile("a.out") { f1 => 
      withFile("b.out") { f2 =>
        f1.println("one")
        f2.println("two")
      }
    }
  }

}



class Local extends CompilerTesting {

  @Test def test10: Unit = {
    def foo(f: Int->Int) = f(1)
    def g(@local x: Int) = 2 // return x should fail
    foo(x => 2*g(x))
  }

  @Test def test11: Unit = expectEscError(
  "value x cannot be used as 1st class value @local[Nothing]", 
  """
    def foo(f: Int->Int) = f(1)
    def g(@local x: Int) = x // return x should fail
    foo(x => 2*g(x))
  """)

  @Test def test12: Unit = {
    class IO
    def println(s:String)(implicit @local io: IO) = { }
    @local val io = new IO
    @local def bar = println("bar")(io)  // ok
  }

  @Test def test13: Unit = expectEscError(
  "value io cannot be used inside method foo", 
  """
    class IO
    def println(s:String)(@local io: IO) = Console.println(s)
    @local val io = new IO
    def foo = println("foo")(io)  // fails
  """)

  @Test def test14: Unit = {
    class IO
    def println(s:String)(implicit @local io: IO) = { }
    implicit @local val io = new IO

//    val foo = () => println("foo")  // fails
    @local val bar = () => println("bar")  // ok

    def handler(@local f: Int => Int) = f(7)

    handler { x => bar(); 2 }
  }

  @Test def test15: Unit = expectEscError(
  "value io cannot be used inside value $anonfun", 
  """
    class IO
    def println(s:String)(implicit @local io: IO) = { }
    implicit @local val io = new IO

    val foo = () => println("foo")  // fails
    @local val bar = () => println("bar")  // ok

    def handler(@local f: Int => Int) = f(7)

    handler { x => bar(); 2 }
  """)

  @Test def test16: Unit = {
    class IO
    def println(s:String)(implicit @local io: IO) = { }
    implicit @local val io = new IO

//    val foo = () => println("foo")  // fails
    @local val bar = () => println("bar")(io)  // ok

    def handler(@local f: Int => Int) = f(7)

    handler { x => bar(); 2 }
 }


  @Test def test17: Unit = {

    abstract class A {
      def foo(@local x: Int): Int
    }

    class B extends A {
      def foo(x: Int): Int = x
    }

    @local val y = 8

    val b: A = new B
    b.foo(y)
  }


  @Test def test18: Unit = {
    val f = new java.io.File("foo")
    val s = ESC.NO(f.getCanonicalPath())
  }

  @Test def test19: Unit = {

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

}




class TryCatch extends CompilerTesting {

  @Test def trycatch1: Unit = { () =>

    def trycatch(@local f: (Exception => Nothing) -> Unit): Unit = ???

    trycatch { raise =>
      raise(new Exception)
    }

  }

  @Test def trycatch2: Unit = { () =>

    def trycatch(@local f: (Exception => Nothing) -> Unit): Unit = ???

    def safeMethod(@local f: () => Unit): Unit = ???

    trycatch { raise =>
      safeMethod { () =>
        raise(new Exception)  // ok
        ()
      }
      ()
    }

  }

  @Test def trycatch3: Unit = { () =>

    def trycatch(@local f: (Exception => Nothing) -> Int): Int = ???

    def safeMethod(f: Unit -> Int): Int = ???

    trycatch { raise =>

      def inner(a:Int): Int = a

      safeMethod { _ =>
        raise(new Exception)  // ok
        inner(7)
      }

      9
    }

  }



  @Test def trycatch4: Unit = expectEscErrorOutput(
  "value raise cannot be used inside value $anonfun",
  """
    def trycatch(@local f: (Exception => Nothing) -> Int): Int = ???

    def safeMethod(@local f: () => Int): Int = ???
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


  @Test def trycatch5: Unit = { () =>
    def trycatch(f: (Exception => Nothing) -> Int): Int = ???

    def safeMethod(f: Unit -> Int): Int @ safe(f) = ???

    trycatch { raise =>

      def inner(a:Int): Int = a

      safeMethod { _ =>
        raise(new Exception)  // ok
        inner(7) // not ok
      }

      7
    }
  }

}
