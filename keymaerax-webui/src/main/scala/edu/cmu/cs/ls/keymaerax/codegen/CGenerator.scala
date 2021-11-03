/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.codegen.CFormulaTermGenerator._
import edu.cmu.cs.ls.keymaerax.codegen.CGenerator._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Name, Signature}

object CGenerator {
  /** Prints a file header */
  def printHeader(modelName: String): String =
    s"""/**************************
       | *${if(modelName.nonEmpty) " " + modelName + ".c" else ""}
       | * Generated by KeYmaera X
       | **************************/
       |
       |""".stripMargin

  /** Prints include statements. */
  val INCLUDE_STATEMENTS: String =
    """#include <math.h>
      |#include <stdbool.h>
      |
      |""".stripMargin

  /** Prints the parameters struct declaration. */
  def printParameterDeclaration(parameters: Set[NamedSymbol]): String = printStructDeclaration("parameters", parameters, "Model parameters")

  /** Prints the state variables struct declaration. */
  def printStateDeclaration(stateVars: Set[BaseVariable]): String = printStructDeclaration("state", stateVars, "State (control choices, environment measurements etc.)")

  /** Prints the input (non-deterministically assigned variables) struct declaration. */
  def printInputDeclaration(inputs: Set[BaseVariable]): String = printStructDeclaration("input", inputs, "Values for resolving non-deterministic assignments in control code")

  /** Prints the verdict struct declaration with documentation comment. */
  def printVerdictDeclaration(): String =
    """/** Monitor verdict: `id` identifies the violated monitor sub-condition, `val` the safety margin (<0 violated, >=0 satisfied). */
      |typedef struct verdict { int id; long double val; } verdict;
      |
      |""".stripMargin
}

/**
  * C++ code generator that prints a file header, include statements, declarations, and the output of `bodyGenerator`.
  * @author Ran Ji
  * @author Stefan Mitsch
  */
class CGenerator(bodyGenerator: CodeGenerator, init: Formula, defs: Declaration) extends CodeGenerator {
  /** Generate C Code for given expression using the data type cDataType throughout and the input list of variables */
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable], fileName: String): (String, String) =
    generateMonitoredCtrlCCode(expr, init, stateVars, inputVars, fileName)

  /** The name of the monitor/control function argument representing monitor parameters. */
  private val FUNC_PARAMS_NAME = "params"

  /** Compiles primitive expressions with the appropriate params/curr/pre struct location. */
  private def primitiveExprGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator({
    case t: Variable =>
      if (parameters.contains(t)) FUNC_PARAMS_NAME + "->"
      else ""
    case FuncOf(fn, Nothing) =>
      if (parameters.contains(fn)) FUNC_PARAMS_NAME + "->"
      else throw new CodeGenerationException("Non-posterior, non-parameter function symbol " + fn.prettyString + " is not supported")
  }, defs)

  /** Prints function definitions of symbols in `mentionedIn`. */
  private def printFuncDefs(mentionedIn: Expression, defs: Declaration, parameters: Set[NamedSymbol], printed: Set[NamedSymbol] = Set.empty): (String, Set[NamedSymbol]) = {
    val what = StaticSemantics.symbols(mentionedIn) -- printed
    val printing = defs.decls.
      filter({
        case (n, s@Signature(_, Real | Bool, Some(_), _, _)) =>
          val sym = Declaration.asNamedSymbol(n, s)
          !parameters.contains(sym) && !printed.contains(sym) && what.contains(sym)
        case _ => false })
    printing.foldLeft(("", printed))({
      case ((result, printed), (name, sig@Signature(_, codomain, Some(args), interpretation, _))) =>
        def ctype(s: Sort): String = s match {
          case Real => "long double"
          case Bool => "bool"
          case _ => throw new IllegalArgumentException("Sort " + s + " not supported")
        }
        val cargs = args.map({ case (n, s) => s"${ctype(s)} ${n.prettyString}" }).mkString(", ")
        //@note ensure that args don't have both . and ._0
        assert(interpretation.forall(StaticSemantics.symbols(_).flatMap({
          case DotTerm(_, Some(i)) => Some(i)
          case DotTerm(_, None) => Some(0)
          case _ => None
        }).count(_ == 0) <= 1))
        val argsSubst = USubst(args.zipWithIndex.flatMap({ case ((Name(n, idx), s), i) =>
          (if (i == 0) List(SubstitutionPair(DotTerm(s, None), Variable(n, idx, s))) else Nil) :+
            SubstitutionPair(DotTerm(s, Some(i)), Variable(n, idx, s)) }))
        val ((interpretationDefs, subPrinted), body) = interpretation match {
          case Some(i) => (printFuncDefs(i, defs, parameters, printed), primitiveExprGenerator(parameters)(argsSubst(i))._2)
          case _ => (("", Set.empty), "0; /* todo */")
        }
        def arguments(x: String): String = "const parameters* const " + FUNC_PARAMS_NAME + (if (x.nonEmpty) ", " + x else "")
        (result + "\n\n" +
          s"""$interpretationDefs
           |${ctype(codomain)} ${name.prettyString}(${arguments(cargs)}) {
           |  return $body;
           |}""".stripMargin,
          printed ++ subPrinted ++ Set(Declaration.asNamedSymbol(name, sig)))
      })
  }

  private def initGenerator(parameters: Set[NamedSymbol]) = new CFormulaTermGenerator({
    case t: Variable if  parameters.contains(t) => "params->"
    case t: Variable if !parameters.contains(t) => "init->"
    case FuncOf(fn, Nothing) if  parameters.contains(fn) => "params->"
    case FuncOf(fn@Function(fname, _, _, _, _), Nothing) if !parameters.contains(fn) && fname.endsWith("post") => "init->"
    case FuncOf(fn, Nothing) if !parameters.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  }, defs)

  /** Generates a monitor `expr` that switches between a controller and a fallback controller depending on the monitor outcome. */
  private def generateMonitoredCtrlCCode(expr: Expression, init: Formula, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable], fileName: String) : (String, String) = {
    val names = StaticSemantics.symbols(expr).map(nameIdentifier)
    require(names.intersect(RESERVED_NAMES).isEmpty, "Unexpected reserved C names encountered: " + names.intersect(RESERVED_NAMES).mkString(","))
    val bodyParameters = CodeGenerator.getParameters(defs.exhaustiveSubst(expr), stateVars)
    val initParameters = CodeGenerator.getParameters(defs.exhaustiveSubst(init), stateVars)
    val parameters = bodyParameters ++ initParameters

    def initTermContainer(expr: Expression, params: Set[NamedSymbol]): String = expr match {
      case t: Variable if  params.contains(t) => "params->"
      case t: Variable if !params.contains(t) => "init->"
      case FuncOf(fn, Nothing) if  params.contains(fn) => "params->"
      case _ => throw new CodeGenerationException("Unsupported symbol " + expr.prettyString + " found in initial conditions " + init.prettyString)
    }

    val initGen = new SimpleMonitorGenerator('resist, defs, CPrettyPrinter, initTermContainer)
    val (initDefs, initBody) = initGen(init, stateVars, inputVars, fileName)
    val (bodyBody, bodyDefs) = bodyGenerator(expr, stateVars, inputVars, fileName)

    val initCheck =
      s"""verdict checkInit(const state* const init, const parameters* const params) {
         |${initBody.linesWithSeparators.map("  " + _).mkString}
         |}""".stripMargin

    val exprDefs = printFuncDefs(expr, defs, parameters)

    (printHeader(fileName) +
      INCLUDE_STATEMENTS +
      printParameterDeclaration(parameters) +
      printStateDeclaration(stateVars) +
      printInputDeclaration(inputVars) +
      printVerdictDeclaration +
      exprDefs._1 +
      printFuncDefs(init, defs, parameters, exprDefs._2)._1 +
      initDefs + "\n" +
      initCheck + "\n" +
      bodyDefs
      ,
      bodyBody)
  }

  private val RESERVED_NAMES = Set("main", "Main")
}