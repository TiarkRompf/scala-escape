package scala.tools.escape

import org.junit.Test

class CompilerTesting {
  private def pluginJar: String = {
    val f = sys.props("scala-escape-plugin.jar")
    assert(new java.io.File(f).exists, f)
    f
  }
  def loadPlugin = s"-Xplugin:${pluginJar} -Xexperimental"

  // note: `code` should have a | margin
  def escErrorMessages(msg: String, code: String) =
    errorMessages(msg, loadPlugin)(s"import scala.util.escape._\nobject Test {\ndef trycatch1: Unit = {\n${code.stripMargin}\n}\n}")

  def expectEscErrorOutput(msg: String, code: String) = {
    val errors = escErrorMessages(msg, code)
//    println("errors:")
//    errors foreach println
    assert((errors mkString "\n") == msg.stripMargin.trim, errors mkString "\n")
  }

  def expectEscError(msg: String, code: String) = {
    val errors = escErrorMessages(msg, code)
    assert(errors exists (_ contains msg), errors mkString "\n")
  }

  def expectEscErrors(msgCount: Int, msg: String, code: String) = {
    val errors = escErrorMessages(msg, code)
    val errorCount = errors.filter(_ contains msg).length
    assert(errorCount == msgCount, s"$errorCount occurrences of \'$msg\' found -- expected $msgCount in:\n${errors mkString "\n"}")
  }

  // TODO: move to scala.tools.reflect.ToolboxFactory
  def errorMessages(errorSnippet: String, compileOptions: String)(code: String): List[String] = {
    import scala.tools.reflect._
    val m = scala.reflect.runtime.currentMirror
    val tb = m.mkToolBox(options = compileOptions) //: ToolBox[m.universe.type]
    val fe = tb.frontEnd

    try {
      tb.eval(tb.parse(code))
      Nil
    } catch {
      case _: ToolBoxError =>
        import fe._
        infos.toList collect { case Info(_, msg, ERROR) => msg }
    }
  }
}
