package scala.tools.escape

import scala.tools.nsc
import nsc.Global
import nsc.plugins.Plugin
import nsc.plugins.PluginComponent

class EscPlugin(val global: Global) extends Plugin {
  val name = "escape"
  val description = "checks escape behavior"

  val escPhase = new {
    val global = EscPlugin.this.global
  } with EscTransform {
    val runsAfter = List("typer")
    override val runsBefore = List("pickler")
  }

  val components = List[PluginComponent](escPhase)

  val checker = new {
    val global: EscPlugin.this.global.type = EscPlugin.this.global
  } with EscAnnotationChecker

  // TODO don't muck up global with unused checkers
  global.addAnnotationChecker(checker.checker)
  global.analyzer.addAnalyzerPlugin(checker.plugin)

  global.log("instantiated escape plugin: " + this)
}
