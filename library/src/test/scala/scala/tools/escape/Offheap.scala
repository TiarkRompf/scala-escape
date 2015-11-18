package scala.tools.escape

import scala.util.escape._
import scala.offheap._

import org.junit.Test
import org.junit.Assert.assertEquals

class MallocSuite extends CompilerTesting {
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
      val data = Array.uninit[Long](n.toInt)

	  val r = new Region {
	    type Cap = Any
	    //var data = Array.uninit[Long](n.toInt)	//Result type in structural refinement may not refer to a user-defined value class
	    											//Solution is to put it outside new Region {} block
	    //var data = Array.uninit[Long](n.toInt).toArray
    	for (i <- 0 until n.toInt) data(i) = 0

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

	@Test def test99 {
		withRegion[Long](100) { r => c0 => 
		  //for @lcoal[Nothing], succeed
		  //for @local[Any]/@local, compile error
     	  @local implicit val c = c0.asInstanceOf[r.Cap] // temporary bug!
		  val a = r.alloc(3)  // type: Data[r.Cap]
		  val b = r.alloc(4)  // how to create a variable of this type outside region?
		  a(0) = 1
		  b(1) = 2
		  println(a(0))
		  println(b(1))
		  -1L
		}
	}
}
