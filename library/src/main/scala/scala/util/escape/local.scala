package scala.util.escape

import scala.annotation.{ Annotation, StaticAnnotation, TypeConstraint }

class safe(xs: Any*) extends StaticAnnotation with TypeConstraint

case object %


/*
Any = 2
Nothing = 1
*/

class local[-T] extends StaticAnnotation with TypeConstraint

trait `->`[-A,+B] extends Function1[A,B] {
  def apply(@local[Any] y: A): B
}

// Note: must be top-level, so compiler phase can detect it by prefix "->"
trait `->*`[P, -A,+B] extends Function1[A,B] {
  def apply(@local[P] y: A): B
}

object ESC {
    def NO[T](x:T):T = x
}
