package scala.tools.escape

import org.junit.{ Ignore, Test }
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

// TODO: `->*` only works from tests if declared outside test/ classpath?
// trait `->*`[P, -A,+B] extends Function1[A,B] {
//   def apply(@local[P] y: A): B
// }

class FinerGrain2ndClassAttempt extends CompilerTesting {
  val lowerDefAndPassthrough = """
    trait Lower extends Any

    def passthroughLower(@local[Lower] fn: Int => Any) = fn(42)
    """

  @Test def testClosureCanAccessFirstClass = expectEscErrorOutput(
    "",
    lowerDefAndPassthrough + """
    @local[Nothing] val fst = 1
    passthroughLower(x => x + fst)
    """)

  @Test def testClosureCannotAccessHigher2ndClass = expectEscErrorOutput(
    "value hi cannot be used inside value $anonfun",
    lowerDefAndPassthrough + """
    @local[Any] val hi = 2
    passthroughLower(x => { hi; () })
    """)

  @Test def testClosureCanAccessSame2ndClass = expectEscErrorOutput(
    "",
    lowerDefAndPassthrough + """
    @local[Lower] val lo = 1
    passthroughLower(x => { lo; () })
    """)

  @Test def testClosureCannotAccessUnrelatedlyPrivileged = expectEscErrorOutput(
    "value sndUnrelated cannot be used inside value $anonfun",
    lowerDefAndPassthrough + """
    trait Unrelated
    @local[Unrelated] val sndUnrelated = 2
    passthroughLower(x => { sndUnrelated; () })
    """)

  val defs = """
    trait Secret extends Any
    trait Public extends Secret // FIXME: nothing prevents type Public = Nothing

    class File {
      def read() = ???  // FIXME: cannot return 2nd-class value: @local[Public]
      def write[T](@local[Public] obj: T) {}
    }
    @local[Public] val file = new File
    """

  @Test def testExposeSecret = expectEscErrorOutput(
    "value secret cannot be used as 1st class value @local[Public]",
    defs + """
    def exposeSecret[U](
      @local[Secret] // allow access to outer secrets
      fn: `->*`[Secret, String, U]
    ) = fn("password")

    exposeSecret { secret =>
      file.read          // ok
      file.write(secret) // error
      () // fool-proof return
    }
    """)

  @Test def testProtectSecret = expectEscErrorOutput(
    "value secret cannot be used as 1st class value @local[Public]",
    defs + """
    def protectSecret[T, U](@local[Secret] obj: T)(
      @local[Public] fn: `->*`[Secret, T, U]) = fn(obj)

    @local[Secret] val outerSecret = "password"

    // user code that attempting to store a secret
    @local[Public] val leakChannel = new {
      def leak(@local[Secret] secret: Any) {}
    }

    leakChannel.leak("upcast to secret")

    protectSecret("anotherPassword") { secret =>
      file.read          // ok
      file.write(secret) // error
      // outerSecret     // error (free var: @local[>:Public])
      // leakChannel // Note: this should fail, as we could call leak()
                     //       Unfortunatly, putting @local[Secret] on fn
                     //       would have the opposite effect; that is,
                     //       no access to outer secrets would be possible
                     // So, we see that hierarchy should be backward for reads,
                     // but then, we would have the problem with writing.
      // leakChannel.leak(secret)  // FIXME: fails becase of a wrong reason:
                                // value secret @local[Any] cannot be used
                                // as 1st class value
                                // @local[...SecretCannotLeak.Secret]
                                   // OR crashes if Secret = Any
      () // fool-proof return
    }
    """)

  @Test def testUpcastToSecret = expectEscErrorOutput(
    "", """
    trait Secret extends Any
    trait Public extends Secret
      // Another way of achieving the above (buggy) behavior
      @local[Public] val sUnprotected = "semi-secret";
      {  // but we can simply up-cast to pretect it against file write
        @local[Secret] val sProtected = sUnprotected
        // file.write(sProtected) // error
      }
    """)

  val multiLevelFileAndSecretDefs = """
    type Public = Any
    trait Secret extends Public

    class File
    def read(@local f: File) = "contents"
    def write(@local[Secret] f: File, s: String) {}

    def exposeSecret[U](  // note: does not permit access to non-Secret files
      @local[Public]  // FIXME: -> makes fn 2nd-class even if we remove @local?
      fn: String => U
    ) = fn("password")
  """

  @Test def testNoWriteSecretToPublicFile = expectEscErrorOutput(
    "value f cannot be used as 1st class value @local[Secret]",
    multiLevelFileAndSecretDefs + """
    @local[Public] val f: File = new File
    exposeSecret { secret =>
      read(f)          // ok
      write(f, secret) // error
    }
    """)

  @Test def testCanWriteSecretToSecretFile = expectEscErrorOutput(
    "",
    multiLevelFileAndSecretDefs + """
    @local[Secret] val f: File = new File
    exposeSecret { secret =>
      read(f)          // ok
      write(f, secret) // ok
    }
    """)

  @Test def testNoWriteInReduce = expectEscErrorOutput(
    """value fDebug cannot be used inside value $anonfun
    """,
    """
    class File(n: String) {
      def readCharAt(idx: Int) = '?'
      def print(xs: Any*) {}
    }

    trait R // (implicitly <:Any and >:Nothing)

    def withFile[U](n: String)(@local fn: File -> U): U = fn(new File(n))
    def withFileR[U](n: String)(@local[R] fn: ->*[R, File, U]): U =
      fn(new File(n))

    def reduce[T](xs: Seq[T])(@local[R] op: (T, T) => T): T =
      xs match {
        case Seq(last) => last
        case _ => op(xs.head, reduce(xs.tail)(op))
      }

    val contents = withFile("/dev/stderr") { fDebug =>
      reduce(Seq("force", "there", "is")) { (chars1, chars2) =>
        fDebug.print(chars1, chars2) // error
        chars1 + chars2
      }
    }
    withFile("/some/chars") { fOut => fOut.print(contents) }

    val pairs = contents.zipWithIndex // e.g., ('i', 0), ('s', 1)
      withFileR("/some/chars") { f =>
        reduce(pairs) { (p1, p2) =>
          val i = (p1._2 + p2._2) / 2
          (f.readCharAt(i), i)  // ok
        }
      }
    """)

  @Test def testDropAccess = expectEscErrorOutput(
    "value passwd cannot be used as 1st class value @local[Nothing]",
    """
    type TopSec = Any
    trait Sec extends TopSec
    type Pub = Nothing

    def dropToSec[U](@local[Sec] body: () => U) = body()
    def dropToPub[U](@local[Pub] body: () => U) = body()

    def cryptoHash(@local[TopSec] passwd: String): String = ???
    def addUser(@local[Sec] email: String): Int = ???
    def setPassword(userId: Int, passwdHash: String) = ???
    def register(@local[Sec] user: String, @local[TopSec] passwd: String) {
      val passwdHash = cryptoHash(passwd) // fully trusted code
      dropToSec { () => // semi-trusted code
        val userId =
          addUser(user)   // ok
        print(passwd)     // error
        dropToPub { () => // untrusted code
          setPassword(userId, passwdHash)
        }
      }
    }
    """)
}

// distinguish between read and write capabilities for files,
// with different escape policies
class FinerGrain2ndClassAttempt2 extends CompilerTesting {
  val defCommon = """
    trait CanWrite
    trait OnePointFive

    def reduce[T](xs: Seq[T])(@local[OnePointFive] f: (T,T) => T) = f(xs(0),xs(1)) // stub
  """

  @Test def testLessPrivilegedFile: Unit = expectEscErrorOutput(
  "value c cannot be used inside value $anonfun",
  defCommon + """
    def main(implicit @local c: CanWrite): Unit = {
      class File(val path: String) {
        def readAll(): String = "<contents>"
        def append(data: String)(implicit @local c: CanWrite): Unit = {}
        def close(): Unit = {}
      }

      def withFile[U](n: String)(@local fn: ->*[OnePointFive,File,U]): U = {
        val f = new File(n); try fn(f) finally f.close()
      }

      withFile("test.out") { f =>
        f.append("contents")
        val len = f.readAll().length
        reduce(Range(0, len)) { (l, r) =>
          val contents = f.readAll()         // ok
          f.append(contents.substring(l, r)) // error
          (l + r) / 2
        }
      }
    }
  """)

  @Test def testNonPrivilegedFile: Unit = expectEscErrorOutput(
  "value out cannot be used inside value $anonfun",
  defCommon + """
    trait CanRead

    class File(val path: String) {
      def readAll()(implicit @local[OnePointFive] c: CanRead) = "<contents>"
      def append(data: String)(implicit @local c: CanWrite): Unit = {}
      def close(): Unit = {}
    }

    def withFileR[U](n: String)(@local fn: File => ->*[OnePointFive,CanRead, U]): U =
      withFile(n) { f => fn(f)(new CanRead {}) }
    def withFileW[U](n: String)(@local fn: File => CanWrite -> U): U =
      withFile(n) { f => fn(f)(new CanWrite {}) }
    def withFile[U](n: String)(@local fn: File => U): U = {
      val f = new File(n); try fn(f) finally f.close()
    }

    withFileW("test.out") { f => implicit out =>
      f.append("contents")
      withFileR("test.out") { fIn => implicit in =>
        val len = fIn.readAll().length
        reduce(Range(0, len)) { (l, r) =>
          val contents = f.readAll()         // ok
          f.append(contents.substring(l, r)) // error
          (l + r) / 2
        }
      }
    }
  """)
}
