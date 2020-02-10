/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import com.wolfram.jlink._
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.{KExpr, MExpr}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaNameConversion._
import edu.cmu.cs.ls.keymaerax.tools.ConversionException

import scala.annotation.tailrec
import scala.collection.immutable._
import scala.math.BigDecimal

// favoring immutable Seqs
import scala.collection.immutable._

/**
  * Converts KeYmaeara X [[edu.cmu.cs.ls.keymaerax.core.Expression expression data structures]]
  * to Mathematica Expr objects.
  * @author Stefan Mitsch
  * @author Nathan Fulton
 */
object KeYmaeraToMathematica extends KeYmaeraToMathematica
class KeYmaeraToMathematica extends K2MConverter[KExpr] {

  /** Backconversion for contracts. */
  def m2k: M2KConverter[KExpr] = MathematicaToKeYmaera

  /**
   * Converts KeYmaera expressions into Mathematica expressions.
   */
  private[tools] def convert(e: KExpr): MExpr = {
    val convertInterpretedSymbols = Configuration.getOption(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS).getOrElse("false").toBoolean
    insist(convertInterpretedSymbols || StaticSemantics.symbols(e).forall({case Function(_, _, _, _, interpreted) => !interpreted case _ => true}),
      "Interpreted functions not allowed in soundness-critical conversion to Mathematica")
    insist(StaticSemantics.symbols(e).forall({case fn@Function(_, _, _, _, true) => interpretedSymbols.contains(fn) case _ => true}),
      "Interpreted functions must have expected domain and sort")
    insist(disjointNames(StaticSemantics.symbols(e)), "Disjoint names required for Mathematica conversion")

    e match {
      case t: Term => convertTerm(t)
      case f: Formula => convertFormula(f)
      case _: Program => throw new IllegalArgumentException("There is no conversion from hybrid programs to Mathematica " + e)
      case _: Function => throw new IllegalArgumentException("There is no conversion from unapplied function symbols to Mathematica " + e)
    }
  }

  /** Checks that the `symbols` are all disjoint names (disallow variable and function of same name).  */
  private[tools] def disjointNames(symbols: Set[NamedSymbol]): Boolean = {
    val names = symbols.map(x => (x.name, x.index)).toList
    names.distinct.length == names.length
  }

  /**
   * Converts a KeYmaera term to a Mathematica expression.
   */
  protected[tools] def convertTerm(t: Term): MExpr = {
    require(t.sort == Real || t.sort == Unit || FormulaTools.sortsList(t.sort).forall(_ == Real), "Mathematica can only deal with reals not with sort " + t.sort)
    t match {
      //@todo Code Review: clean up FuncOf conversion into two cases here
      //@solution: inlined and simplified the FuncOf cases, moved uniform name conversion into MathematicaNameConversion
      //@solution: distinguish between interpreted and uninterpreted function symbols
      //@note Uninterpreted functions are mapped to namespace kyx` to avoid clashes with any interpreted names
      case FuncOf(fn, child) =>
        if (fn.interpreted) interpretedSymbols(fn)(convertFunctionArgs(child))
        else MathematicaOpSpec.func.k2m(fn, convertFunctionArgs(child))
      case Neg(c) => MathematicaOpSpec.neg(convertTerm(c))
      case Plus(l, r) => MathematicaOpSpec.plus(convertTerm(l), convertTerm(r))
      case Minus(l, r) => MathematicaOpSpec.minus(convertTerm(l), convertTerm(r))
      case Times(l, r) => MathematicaOpSpec.times(convertTerm(l), convertTerm(r))
      case Divide(l: Number, r: Number) =>
        if (l.value.isValidLong && r.value.isValidLong) MathematicaOpSpec.rational(convertTerm(l), convertTerm(r))
        else MathematicaOpSpec.divide(convertTerm(l), convertTerm(r))
      case Divide(l, r) => MathematicaOpSpec.divide(convertTerm(l), convertTerm(r))
      case Power(l, r) => MathematicaOpSpec.power(convertTerm(l), convertTerm(r))
      case Number(n) =>
        if (n.isWhole) {
          MathematicaOpSpec.bigInt(n.toBigIntExact().getOrElse(
            throw new ConversionException("Unexpected: whole BigDecimal cannot be converted to BigInteger")))
        } else if (n.scale > 0) {
          val num = BigDecimal(n.bigDecimal.unscaledValue())
          val denom = BigDecimal(BigDecimal(1).bigDecimal.movePointRight(n.scale))
          assert(n == num/denom, "Expected double to rational conversion to have value " + n + ", but got numerator " + num + " and denominator " + denom)
          MathematicaOpSpec.rational(convert(Number(num)), convert(Number(denom)))
        } else if (n.scale < 0) {
          //@note negative scale means: unscaled*10^(-scale)
          val num = BigDecimal(n.bigDecimal.unscaledValue()).bigDecimal.movePointLeft(n.scale)
          assert(n == BigDecimal(num), "Expected double conversion to have value " + n + ", but got " + num)
          convert(Number(num))
        } else throw new ConversionException("Number is neither BigInteger nor encodable as rational of BigInteger: " + n)
      case t: Variable => toMathematica(t)
      case Pair(l, r) => MathematicaOpSpec.pair(convertTerm(l), convertTerm(r))
    }
  }

  /** Converts KeYmaera formulas into Mathematica expressions. */
  protected def convertFormula(f: Formula): MExpr = f match {
    case And(l, r)  => MathematicaOpSpec.and(convertFormula(l), convertFormula(r))
    case Equiv(l,r) => MathematicaOpSpec.equivalent(convertFormula(l), convertFormula(r))
    case Imply(l,r) => MathematicaOpSpec.implies(convertFormula(l), convertFormula(r))
    case Or(l, r)   => MathematicaOpSpec.or(convertFormula(l), convertFormula(r))
    case Equal(l,r) => MathematicaOpSpec.equal(convertTerm(l), convertTerm(r))
    case NotEqual(l,r) => MathematicaOpSpec.unequal(convertTerm(l), convertTerm(r))
    case LessEqual(l,r) => MathematicaOpSpec.lessEqual(convertTerm(l), convertTerm(r))
    case Less(l,r)   => MathematicaOpSpec.less(convertTerm(l), convertTerm(r))
    case GreaterEqual(l,r) => MathematicaOpSpec.greaterEqual(convertTerm(l), convertTerm(r))
    case Greater(l,r) => MathematicaOpSpec.greater(convertTerm(l), convertTerm(r))
    case False => MathematicaOpSpec.lfalse.op
    case True => MathematicaOpSpec.ltrue.op
    case Not(phi) => MathematicaOpSpec.not(convertFormula(phi))
    case exists: Exists => convertQuantified(exists, MathematicaOpSpec.exists)
    case forall: Forall => convertQuantified(forall, MathematicaOpSpec.forall)
    case _ => throw new ConversionException("Don't know how to convert " + f + " of class " + f.getClass)
  }

  /** Converts a quantified formula. */
  protected def convertQuantified(f: Quantified, op: QuantifiedMathOpSpec): MExpr = {
    /** Recursively collect quantified variables, return variables+child formula */
    @tailrec
    def collectVars(vsSoFar: Array[NamedSymbol], candidate: Formula): (Array[NamedSymbol], Formula) = (f, candidate) match {
      // collect only from quantifiers that are the same as the root `f` quantifier
      case (_: Exists, Exists(nextVs, nextf)) => collectVars(vsSoFar ++ nextVs, nextf)
      case (_: Forall, Forall(nextVs, nextf)) => collectVars(vsSoFar ++ nextVs, nextf)
      case _ => (vsSoFar, candidate)
    }

    val (vars, formula) = collectVars(f.vars.toArray, f.child)
    op(vars.map(toMathematica), convertFormula(formula))
  }

  /** Convert function arguments. */
  private[this] def convertFunctionArgs(args: Term): Array[Expr] = args match {
    case _: Pair =>
      val converted = convertTerm(args)
      assert(converted.listQ(), "Converted pair expected to be a list, but was " + converted)
      converted.args()
    case Nothing => Array.empty[MExpr]
    case _ => Array[MExpr](convertTerm(args))
  }
}
