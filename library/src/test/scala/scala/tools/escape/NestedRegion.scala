package scala.tools.escape

import scala.util.escape._
import scala.offheap._

import org.junit.Test
import org.junit.Assert.assertEquals

trait NestedRegions[LT] { // LT = Any -> use @local, LT = Nothing -> ignore it
  type plocal = local[LT]
  //need modification
  trait Data[T] {
    def size: Long
    def apply(i: Long)(implicit @plocal cc: T): Long
    def update(i: Long, x:Long)(implicit @plocal cc: T): Unit
  }
  trait Region {
    type Cap
    def alloc(n: Long)(implicit @plocal c: Cap): Data[Cap]
  }

  abstract class F[B] { def apply(r: Region): r.Cap -> B }

  def withRegion[T](n: Long)(f: F[T]): T = {
    implicit val allocator: Allocator = malloc
    //pay attention not to access outOfBoundary?
    object cap
    val data = Array.uninit[Long](n.toInt) //malloc(n) // FIXME(Xilun) If we put it inside, we would get: Result type in structural refinement may not refer to a user-defined value class
    val r = new Region {
      type Cap = cap.type
      var p = 0L
      def alloc(n: Long)(implicit @plocal c: Cap) = new Data[Cap] {
	def size = n
	val addr = p
	p += n
	def apply(i: Long)(implicit @plocal c: Cap): Long =
	  data((addr+i).toInt)
	def update(i: Long, x:Long)(implicit @plocal cc: Cap): Unit =
	  data((addr+i).toInt) = x
      }
    }
    try f(r)(cap) finally allocator.free(data.addr) //free(r.data)
  }
}
