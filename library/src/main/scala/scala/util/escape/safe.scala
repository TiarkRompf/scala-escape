package scala.util.escape

import scala.annotation.{ Annotation, StaticAnnotation, TypeConstraint }

class safe(xs: Any*) extends StaticAnnotation with TypeConstraint

case object %