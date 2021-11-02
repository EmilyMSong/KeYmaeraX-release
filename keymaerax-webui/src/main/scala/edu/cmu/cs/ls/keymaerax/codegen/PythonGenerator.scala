/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.codegen

import edu.cmu.cs.ls.keymaerax.codegen.PythonPrettyPrinter.{nameIdentifier, printSort}
import edu.cmu.cs.ls.keymaerax.codegen.PythonGenerator.{IMPORT_STATEMENTS, printHeader, printInputDeclaration, printParameterDeclaration, printStateDeclaration, printVerdictDeclaration}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Name, Signature}

/**
  * Python code generator header and declaration printing.
  * @author Stefan Mitsch
  */
object PythonGenerator {
  val RESERVED_NAMES = Set("self", "in", "val", "bool", "def", "int", "float")

  /** Prints a file header */
  def printHeader(modelName: String): String =
    s"""#
       |# ${if(modelName.nonEmpty) modelName + ".py" else ""}
       |# Generated by KeYmaera X
       |#
       |
       |""".stripMargin

  /** Prints import statements. */
  val IMPORT_STATEMENTS: String =
    """from typing import Callable
      |import numpy as np
      |
      |""".stripMargin

  /** Prints a class declaration of class `name` with `fields` and documentation `comment`. */
  def printClassDeclaration[T <: NamedSymbol](name: String, fields: Set[T], comment: String): String = {
    val sortedVars = fields.toList.sorted[NamedSymbol]
    val names = sortedVars.map({
      case x: Variable => nameIdentifier(x) -> printSort(x.sort)
      case f: Function =>
        assert(!CodeGenerator.isInterpreted(f), "Parameter must not be an interpreted function")
        assert(f.domain == Unit, "If declared as function, parameter must have domain Unit, but has " + f.domain)
        nameIdentifier(f) -> printSort(f.sort)
    })
    val fieldDecls = names.map({ case (n, s) => n + ": " + s })
    val setFields = names.map(_._1).map(s => s"self.$s = $s")
    val printFields = names.map(_._1).map(s => s""""$s=" + str(self.$s)""").mkString(""" + ", " + """)
    val body = if (names.isEmpty) "self" else setFields.mkString("\n    ")
    s"""# $comment
       |class $name:
       |  def __init__(self${{if (fieldDecls.nonEmpty) ", " else ""} + fieldDecls.mkString(", ")}):
       |    $body
       |  def __str__(self) -> str:
       |    return "$name(" + ${if (names.nonEmpty) printFields + " + " else ""} ")"
       |
       |""".stripMargin
  }

  /** Prints the parameters class declaration. */
  def printParameterDeclaration(parameters: Set[NamedSymbol]): String = printClassDeclaration("Params", parameters, "Model parameters")

  /** Prints the state variables class declaration. */
  def printStateDeclaration(stateVars: Set[BaseVariable]): String = printClassDeclaration("State", stateVars, "State (control choices, environment measurements etc.)")

  /** Prints the input (non-deterministically assigned variables) class declaration. */
  def printInputDeclaration(inputs: Set[BaseVariable]): String = printClassDeclaration("Input", inputs, "Values for resolving non-deterministic assignments in control code")

  /** Prints the verdict class declaration. */
  def printVerdictDeclaration(): String = printClassDeclaration("Verdict", Set(Variable("id"), Variable("val")), "Verdict identifier and value")
}

/**
  * Python code generator that prints a file header, include statements, declarations, and the output of `bodyGenerator`.
  * @author Stefan Mitsch
  */
class PythonGenerator(bodyGenerator: CodeGenerator, init: Formula = True, defs: Declaration = Declaration(Map.empty)) extends CodeGenerator {
  /** Generate Python code for given expression using the data type cDataType throughout and the input list of variables */
  override def apply(expr: Expression, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable], fileName: String): (String, String) =
    generateMonitoredCtrlCCode(expr, init, stateVars, inputVars, fileName)

  /** The name of the monitor/control function argument representing monitor parameters. */
  private val FUNC_PARAMS_NAME = "params"

  /** Compiles primitive expressions with the appropriate params/curr/pre struct location. */
  private def primitiveExprGenerator(parameters: Set[NamedSymbol]) = new PythonFormulaTermGenerator({
    case t: Variable =>
      if (parameters.contains(t)) FUNC_PARAMS_NAME + "."
      else ""
    case FuncOf(fn, Nothing) =>
      if (parameters.contains(fn)) FUNC_PARAMS_NAME + "."
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
        def ptype(s: Sort): String = s match {
          case Real => "np.float64"
          case Bool => "bool"
          case _ => throw new IllegalArgumentException("Sort " + s + " not supported")
        }
        val pargs = args.map({ case (n, s) => s"${n.prettyString}: ${ptype(s)}" }).mkString(", ")
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
          case _ => (("", Set.empty), PythonPrettyPrinter.numberLiteral(0.0) + " # todo")
        }
        def arguments(x: String): String = FUNC_PARAMS_NAME + ": Params" + (if (x.nonEmpty) ", " + x else "")
        (result + (if (interpretationDefs.trim.isEmpty) "\n" else "\n\n") +
          s"""$interpretationDefs
           |def ${name.prettyString}(${arguments(pargs)}) -> ${ptype(codomain)}:
           |  return $body
           |""".stripMargin,
          printed ++ subPrinted ++ Set(Declaration.asNamedSymbol(name, sig)))
    })
  }

  private def initGenerator(parameters: Set[NamedSymbol]) = new PythonFormulaTermGenerator({
    case t: Variable if  parameters.contains(t) => "params."
    case t: Variable if !parameters.contains(t) => "init."
    case FuncOf(fn, Nothing) if  parameters.contains(fn) => "params."
    case FuncOf(fn@Function(fname, _, _, _, _), Nothing) if !parameters.contains(fn) && fname.endsWith("post") => "init."
    case FuncOf(fn, Nothing) if !parameters.contains(fn) && !fn.name.endsWith("post") =>
      throw new CodeGenerationException("Non-posterior, non-parameter function symbol is not supported")
  }, defs)

  /** Generates a monitor `expr` that switches between a controller and a fallback controller depending on the monitor outcome. */
  private def generateMonitoredCtrlCCode(expr: Expression, init: Formula, stateVars: Set[BaseVariable], inputVars: Set[BaseVariable], fileName: String) : (String, String) = {
    val names = StaticSemantics.symbols(expr).map(nameIdentifier)
    require(names.intersect(PythonGenerator.RESERVED_NAMES).isEmpty, "Unexpected reserved Python names encountered: " +
      names.intersect(PythonGenerator.RESERVED_NAMES).mkString(","))
    val bodyParameters = CodeGenerator.getParameters(defs.exhaustiveSubst(expr), stateVars)
    val initParameters = CodeGenerator.getParameters(defs.exhaustiveSubst(init), stateVars)
    val parameters = bodyParameters ++ initParameters

    val (_, initDefs) = bodyGenerator(init, stateVars, inputVars, fileName)
    val initBody = initGenerator(parameters)(init)._2
    val (bodyBody, bodyDefs) = bodyGenerator(expr, stateVars, inputVars, fileName)

    val initCheck =
      s"""def checkInit(init: State, params: Params) -> bool:
         |  return $initBody
         |""".stripMargin

    val exprDefs = printFuncDefs(expr, defs, parameters)

    (printHeader(fileName) +
      IMPORT_STATEMENTS +
      printParameterDeclaration(parameters) +
      printStateDeclaration(stateVars) +
      printInputDeclaration(inputVars) +
      printVerdictDeclaration +
      exprDefs._1 +
      printFuncDefs(init, defs, parameters, exprDefs._2)._1 +
      initDefs +
      initCheck +
      bodyDefs
      ,
      bodyBody)
  }
}