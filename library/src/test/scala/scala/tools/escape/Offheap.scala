package scala.tools.escape

import scala.util.escape._
import scala.offheap._

import org.junit.Test
import org.junit.Assert.assertEquals

class RegionMallocSuite extends CompilerTesting {
  trait Data[T] {
    def size: Long
    def apply(i: Long)(implicit @local cc: T): Long
    def update(i: Long, x:Long)(implicit @local cc: T): Unit
  }
  trait Region {
    type Cap
    def alloc(n: Long)(implicit @local c: Cap): Data[Cap]
  }

  abstract class F[B] { def apply(r: Region): r.Cap -> B }

  def withRegion[T](n: Long)(f: F[T]): T = {
    implicit val allocator: Allocator = malloc
    //pay attention not to access outOfBoundary?
    object cap
    val data = Array.uninit[Long](n.toInt) //malloc(n)
    val r = new Region {
      type Cap = cap.type
      var p = 0L
      def alloc(n: Long)(implicit @local c: Cap) = new Data[Cap] {
      	def size = n
      	val addr = p
      	p += n
      	def apply(i: Long)(implicit @local c: Cap): Long =
      	  data((addr+i).toInt)
      	def update(i: Long, x:Long)(implicit @local cc: Cap): Unit =
      	  data((addr+i).toInt) = x
      }
    }
    try f(r)(cap) finally allocator.free(data.addr) //free(r.data)
  }

  @Test def test101 {
    withRegion[Long](1000) { r => c0 =>
      //for @lcoal[Nothing], succeed
      //for @local[Any]/@local, compile error
      @local implicit val c = c0.asInstanceOf[r.Cap] // temporary bug!
      val a = r.alloc(300)  // type: Data[r.Cap]
      val b = r.alloc(400)  // how to create a variable of this type outside region?
      a(0) = 1
      b(1) = 2
      assert(a(0) == 1)
      assert(b(1) == 2)
      -1L
    }
  }

  @Test def test100 {
    var aa: Data[_] = null
    withRegion[Long](100) { r => c0 =>
      //for @lcoal[Nothing], succeed
      //for @local[Any]/@local, compile error
      @local implicit val c = c0.asInstanceOf[r.Cap] // temporary bug!
      val a = r.alloc(3)  // type: Data[r.Cap]
        aa = a
      a(0) = 1
      //println(a(0))
      assert(a(0) == 1)
      -1L
    }
    val size = aa.size
    assert(size == 3)
    //println("size of data = " + size)
    //		println(aa(0))		//error: accessing outside the scope. Couldn't find implicit parameter
  }
}

/*
 no @local
 */
class OutRegionMallocUnsafeSuite extends CompilerTesting{
  trait Data[T] {
    def size: Long
    def apply(i: Long)(implicit cc: T): Long
    def update(i: Long, x:Long)(implicit cc: T): Unit
  }
  trait Region {
    type Cap
    def alloc(n: Long)(implicit c: Cap): Data[Cap]
  }

  abstract class F[B] { def apply(r: Region): r.Cap -> B }

  def withRegion[T](n: Long)(f: F[T]): T = {
    implicit val allocator: Allocator = malloc
    //pay attention not to access outOfBoundary?
    object cap
    val data = Array.uninit[Long](n.toInt) //malloc(n)
    val r = new Region {
      type Cap = cap.type
      var p = 0L
      def alloc(n: Long)(implicit c: Cap) = new Data[Cap] {
      	def size = n
      	val addr = p
      	p += n
      	def apply(i: Long)(implicit c: Cap): Long =
      	  data((addr+i).toInt)
      	def update(i: Long, x:Long)(implicit cc: Cap): Unit =
      	  data((addr+i).toInt) = x
      }
    }
    try f(r)(cap) finally allocator.free(data.addr) //free(r.data)
  }

  // FIXME(Xilun): Undeterministic? Sometimes IndexOutOfBoundsException
  /*
  @Test def test102 = {
    //pass region and Cap outside scope
    println("test102")
    var a: Data[_] = null
    var rr: Region = null
    withRegion[Long](1000) { r => c0 =>
      implicit val c = c0.asInstanceOf[r.Cap] // temporary bug!
      val b = r.alloc(300)  // type: Data[r.Cap]
        a = b
      b(0) = 1
      println(b(0))
      rr = r   	//pass region r to outside
      -1L
    }
    println("size of data: " + a.size)
    val r = rr
    object cap
    implicit val c = cap.asInstanceOf[r.Cap]
    val aa: Data[r.Cap] = r.alloc(400)
    aa(0) = 2
    println(aa(0))
    //		r.data = null
  }
  */
}

class OutRegionMallocSuite extends CompilerTesting{
  @Test def test103 = expectEscErrorOutput(
"""could not find implicit value for parameter c: r.Cap
could not find implicit value for parameter cc: r.Cap
could not find implicit value for parameter cc: r.Cap""",
    """
  	import scala.offheap._

	trait Data[T] {
	  def size: Long
	  def apply(i: Long)(implicit @local cc: T): Long
	  def update(i: Long, x:Long)(implicit @local cc: T): Unit
	}
	trait Region {
	  type Cap
	  def alloc(n: Long)(implicit @local c: Cap): Data[Cap]
	}

	abstract class F[B] { def apply(r: Region): r.Cap -> B }

	def withRegion[T](n: Long)(f: F[T]): T = {
	  implicit val allocator: Allocator = malloc
	  //pay attention not to access outOfBoundary?
	  var data = Array.uninit[Long](n.toInt) //malloc(n)
	  object cap
	  val r = new Region {
	    type Cap = cap.type
	    var p = 0L
	    def alloc(n: Long)(implicit @local c: Cap) = new Data[Cap] {
	      def size = n
	      val addr = p
	      p += n
	      def apply(i: Long)(implicit @local c: Cap): Long =
	        data((addr+i).toInt)
	      def update(i: Long, x:Long)(implicit @local cc: Cap): Unit =
	        data((addr+i).toInt) = x
	    }
	  }
	  try f(r)(cap) finally allocator.free(data.addr) //free(r.data)
	}
  //pass region and Cap outside scope
	println("test103")
	var a: Data[_] = null
	var rr: Region = null
	var cc: Any = null
	withRegion[Long](1000) { r => c0 =>
  		@local implicit val c = c0.asInstanceOf[r.Cap] // temporary bug!
  		cc = c
  		val b = r.alloc(300)  // type: Data[r.Cap]
  		a = b
  		b(0) = 1
  		println(b(0))
		rr = r   	//pass region r to outside
		-1L
	}
	println("size of data: " + a.size)
	val r = rr
	/*	if we create a new cap, then we'll be able to access data within region
	object cap
	@local implicit val c = cap.asInstanceOf[r.Cap]
	*/
	/*	if we reuse the cap created within region, it fails to CompilerTesting	*/
	val c = cc.asInstanceOf[r.Cap]	//val c = cc also fails
	val aa: Data[r.Cap] = r.alloc(400)
	aa(0) = 2
	println(aa(0))
	""")
}
