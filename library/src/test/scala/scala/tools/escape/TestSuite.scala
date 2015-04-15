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
    "value x not safe (not declared as such by return type of f = (a: Int)Int!\n"+
    "couldn't prove that object returned from f(a) does not point to Set(value x)",
  """
    val x = 100
    val y = 99

    def f(a:Int): Int = a
    def g(a:Int): Int @safe(x) = f(a) // not safe
  """)

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



  @Test def trycatch4 = expectEscErrorOutput(
    "value raise not safe (free in lambda)!","""

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

  @Test def trycatch5 = expectEscErrorOutput(
    "couldn't prove that object returned from inner(7) does not point to Set(value raise)","""

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