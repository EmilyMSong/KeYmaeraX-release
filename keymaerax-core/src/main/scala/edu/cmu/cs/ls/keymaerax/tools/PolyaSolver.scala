/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import java.io.{FileWriter, FileOutputStream, File, InputStream}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, ParseException, KeYmaeraXParser}
import scala.collection.immutable
import scala.sys.process._

/**
 * Created by ran on 4/24/15.
 * @author Ran Ji
 */
class PolyaSolver extends SMTSolver {
  private val DEBUG = System.getProperty("DEBUG", "true")=="true"

  private val converter = DefaultSMTConverter

  /** Get the absolute path to Polya jar */
  private val pathToPolya : String = {
    val polyaTempDir = System.getProperty("user.home") + File.separator + ".keymaerax"
    if(!new File(polyaTempDir).exists) new File(polyaTempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)

    // so far only for Mac Os and linux
    //@todo: support for other OS
    if(new File(polyaTempDir+"polya").exists()) {
      polyaTempDir+"polya"
    } else {
      val osArch = System.getProperty("os.arch")
      var resource : InputStream = null
      if(osName.contains("mac")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/polya/mac64/polya")
        }
      } else if(osName.contains("linux")) {
        if(osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/polya/ubuntu64/polya")
        }
      } else {
        throw new Exception("Polya solver is currently not supported in your operating system.")
      }
      if(resource == null)
        throw new Exception("Could not find Polya in classpath: " + System.getProperty("user.dir"))

      val polyaSource = Channels.newChannel(resource)
      val polyaTemp = new File(polyaTempDir, "polya")
      // Get a stream to the script in the resources dir
      val polyaDest = new FileOutputStream(polyaTemp)
      // Copy file to temporary directory
      polyaDest.getChannel.transferFrom(polyaSource, 0, Long.MaxValue)
      val polyaAbsPath = polyaTemp.getAbsolutePath
      Runtime.getRuntime.exec("chmod u+x " + polyaAbsPath)
      polyaSource.close()
      polyaDest.close()
      assert(new File(polyaAbsPath).exists())
      polyaAbsPath
    }
  }


  /**
   * Get result from Polya output
   *
   * @param output Polya output of the form:
   *                  command
   *                  information
   *                  -----
   *                  input
   *                  -----
   *                  result
   *
   * @return result
   */
  private def getTruncatedResult(output: String) : String = {
    var reversedOutput = output.reverse
    while(reversedOutput.startsWith("\n")) {
      reversedOutput = reversedOutput.stripPrefix("\n")
    }
    val reversedResult = reversedOutput.substring(0, reversedOutput.indexOf("\n"))
    reversedResult.reverse
  }

  /** Return Polya QE result and the proof evidence */
  def qeEvidence(f: Formula) : (Formula, Evidence) = {
    val smtCode = converter(f) + "\n(check-sat)\n"
    if (DEBUG) println("[Solving with Polya...] \n" + smtCode)
    val smtFile = File.createTempFile("polyaQe", ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToPolya + " " + smtFile.getAbsolutePath
    /** Polya output as String, (check-sat) gives 1, -1 or 0 */
    val polyaOutput = cmd.!!
    if (DEBUG) println("[Polya result] \n" + polyaOutput)
    val polyaResult = getTruncatedResult(polyaOutput)
    /** Interpretation of Polya output as KeYmaera X formula
      * if Polya output is 1, then return True
      * if Polya output is -1 or 0, then throw exception
      * Polya does not have other possible result for (check-sat)
      */
    if (polyaResult.equals("-1")) throw new SMTQeException("QE with Polya gives -1 (POSSIBLY SAT). Cannot reduce the following formula to True:\n" + KeYmaeraXPrettyPrinter(f) + "\n")
    else if(polyaResult.equals("1")) (True, ToolEvidence(immutable.List("input" -> smtCode, "output" -> polyaOutput)))
    else if(polyaResult.equals("0")) throw new SMTQeException("QE with Polya gives 0 (FAILED). Cannot reduce the following formula to True:\n" + KeYmaeraXPrettyPrinter(f) + "\n")
    else throw new SMTConversionException("Conversion of Polya result \n" + polyaResult + "\n is not defined")
  }

  /**
   * Simplify a KeYmaera X term into a possibly simple term
   * @param t  KeYmaera X term to be simplified
   * @return   the simplified term, or the original term if the simplify result is not a parsable KeYmaera X term
   */
  def simplify(t: Term) : Term = {
    val smtCode = converter.generateSimplify(t)
    if (DEBUG) println("[Simplifying with Polya ...] \n" + smtCode)
    val smtFile = File.createTempFile("polyaSimplify", ".smt2")
    val writer = new FileWriter(smtFile)
    writer.write(smtCode)
    writer.flush()
    writer.close()
    val cmd = pathToPolya + " " + smtFile.getAbsolutePath
    val polyaOutput = cmd.!!
    if (DEBUG) println("[Polya simplify result] \n" + polyaOutput + "\n")
    val polyaResult = getTruncatedResult(polyaOutput)
    try {
      KeYmaeraXParser.termParser(polyaResult)
    } catch {
      case e: ParseException =>
        if (DEBUG) println("[Info] Cannot parse Polya simplified result: " + polyaResult)
        t
    }
  }
}

