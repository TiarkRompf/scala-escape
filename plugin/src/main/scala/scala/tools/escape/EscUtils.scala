package scala.tools.escape

import scala.tools.nsc.Global
trait EscUtils {
  val global: Global
  import global._

  val verbose: Boolean = System.getProperty("escVerbose", "false") == "true"
  val debug: Boolean = System.getProperty("escDebug", "false") == "true"
  def vprintln(x: =>Any): Unit = if (verbose) println(x)
  def dprintln(x: =>Any): Unit = if (debug) println(x)


  lazy val MarkerSafe = rootMirror.getRequiredClass("scala.util.escape.safe")
  lazy val MarkerLocal = rootMirror.getRequiredClass("scala.util.escape.local")

  protected def newSafeMarker() = newMarker(MarkerSafe)
  protected def newLocalMarker() = newMarker(MarkerLocal)
  protected def newLocalMarker(tpe: Type) = newMarker(appliedType(MarkerLocal, tpe))
  protected def newMarker(tpe: Type): AnnotationInfo = AnnotationInfo marker tpe
  protected def newMarker(sym: Symbol): AnnotationInfo = AnnotationInfo marker sym.tpe

  // annotation checker

  protected def hasSafeMarker(tpe: Type)   = tpe hasAnnotation MarkerSafe
  protected def hasLocalMarker(tpe: Type)   = tpe hasAnnotation MarkerLocal

  def filterAttribs(tpe:Type, cls:Symbol) =
    tpe.annotations filter (_ matches cls)

  def removeAttribs(tpe: Type, classes: Symbol*) =
    tpe filterAnnotations (ann => !(classes exists (ann matches _)))


  // TODO: proper symbol ref
  def isPercentMarker(x: Symbol) = x.toString == "object %"

  def safeArgAnn(tpe: Type) = filterAttribs(tpe, MarkerSafe).flatMap { 
    case AnnotationInfo(_, args, _) =>
      args flatMap { 
        case t@Ident(_) => t.symbol::Nil 
        case t if isPercentMarker(t.symbol) => t.symbol::Nil
        case t => error("wrong shape of @safe annotation: " + t); Nil
      }
  }.toSet



}
