/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Proof data structures for Kaisar
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.Metric
import edu.cmu.cs.ls.keymaerax.core._

object KaisarProof {
  // Identifiers for  proof-variables. Source-level variables are typically alphabetic, elaboration can introduce
  // indices  <alpha><int>
  type Ident = String
  // Identifiers for line labels, which are typically alphabetic
  type TimeIdent = String
  type Statements = List[Statement]

  // Kaisar extends the syntax of expressions with located expressions  f@L.
  // Rather than extend Expression,scala, we implement this as an interpreted function symbol at(f, L()) which
  // we elaborate to the core expression syntax
  // "init" is an example label-function which can be passed for the second argument of at()
  // In concrete proofs, the label function name is generated from the labels in the proof.
  val at: Function = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
  val init: FuncOf = FuncOf(Function("init", domain = Unit, sort = Unit, interpreted = true), Nothing)

  // Special functions max, min, and abs are already used in KeYmaera X, but are often used in Kaisar proofs as well
  val max: Function = Function("max", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val min: Function = Function("min", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val abs: Function = Function("abs", domain = Real, sort = Real, interpreted = true)

  // We reuse expression syntax for patterns over expressions. We use an interpreted function wild() for the wildcard
  // patttern "*" or "_". This is elaborated before proofchecking
  val wild: FuncOf = FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing)

  // Proof statement Block() sequences a list of statements. [[flatten]] flattens the tree structure induced by the
  // [[Block]] constructor.
  def flatten(ss: Statements): Statements = {
    ss match {
      case Block(ss) :: sss  => flatten(ss ++ sss)
      case s :: ss => s :: flatten(ss)
      case Nil => Nil
    }
  }

  // smart constructor for [[Block]] which will [[flatten]] the tree structure
  def block(ss: Statements): Statement = {
    flatten(ss) match {
      case List(s) => s
      case ss => Block(ss)
    }
  }

}

// Umbrella trait for all syntactic classes of abstract syntax tree
sealed trait ASTNode {
  // Location in source file of connective which generated AST node.
  // Populated by parser and used to reconstruct error messages.
  var location: Option[Int] = None
  def setLocation(loc: Int): Unit = { location = Some(loc)}
}

//@TODO Eliminate: redundant with Block
final case class Proof(ss: List[Statement])

// A proof-method expresses a single step of unstructured heuristic proof,
// generally as justification of a single step of some structured proof.
sealed trait Method extends ASTNode
// constructive real-closed field arithmetic
case class RCF() extends Method {}
// general-purpose auto heuristic
case class Auto() extends Method {}
// propositional steps
case class Prop() extends Method {}
// introduce an assumption used in method
case class Using(use: List[Selector], method: Method) extends Method {}
// discharge goal with structured proof
case class ByProof(proof: Proof) extends Method {}

// Forward-chaining natural deduction proof term.
sealed trait ProofTerm extends ASTNode
// Hypothesis rule. Identifier x can be either a proof variable in the current context or a built-in natural-deduction
// rule from the CdGL proof calculus.
// @TODO: Implement the built-in proof calculus rules
case class ProofVar(x: Ident) extends ProofTerm {}
// Term used to instantiatiate a universal quantifier. Should only ever appear on the right-hand side of an application,
// but parsing is simpler when terms are a standalone constructor
case class ProofInstance(e: Expression) extends ProofTerm {}
// Given proof term m, supply n as an argument. Since n can be [[ProofInstance]], the same connective
// [[ProofApp]] supports both modus ponens and universal quantifier instantiation.
case class ProofApp(m: ProofTerm, n: ProofTerm) extends ProofTerm {}

// Selectors are used in unstructured proof step heuristics to indicate which facts should be supplied as hypotheses
// @TODO: Can this be flattened into proofTerm language?
sealed trait Selector extends ASTNode
// Select the result of some proof term, often but not need be a variable
case class ForwardSelector(forward: ProofTerm) extends Selector {}
// Select [[all]] elements of the context which unify with an expression
// @TODO: probably more useful to mean "all which contain e as a subexpression"
// @TODO: Makes early elaboration passes annoying, perhaps implement this later
case class PatternSelector(e: Expression) extends Selector {}

// Pattern language for left-hand side of assignment proofs. Expressions are used for most patterns, but assignment
// patterns are not quite expressions because each assigned variable may introduce a proof variable.
sealed trait AsgnPat extends ASTNode
// @TODO: Ever needed? Used where patterns are optional
case class NoPat() extends AsgnPat
// Wildcard pattern for ignored assignments
case class WildPat() extends AsgnPat
// @TODO: make ident optional for assignments. Is backwards.
// Assign to variable and optionally store equation in a proof variable
case class VarPat(p: Ident, x: Option[Variable] = None) extends AsgnPat
// Assign elements of tuple according to each component pattern
case class TuplePat(pats: List[AsgnPat]) extends AsgnPat

/* Language of structured proofs. Statements are block-structu  red, so entire proofs are single statements */
sealed trait Statement extends ASTNode
// x is a formula pattern in assume and assert
// Assume introduces assumption that f is true, with name(s) given by pattern [[pat]]
case class Assume(pat: Expression, f: Formula) extends Statement
// Assertion proves formula f to be true with method m, then introduces it with name(s) given by pattern [[pat]]
case class Assert(pat: Expression, f: Formula, m: Method) extends Statement
// Modifies the variables specified by [[pat]] by executing [[hp]]. Pattern [[pat]] optionally specifies proof variable
// where equalities induced by assignments are stored. When [[hp==Left(f)]] the assignment is deterministic to term f,
// when [[hp==Right(())]] the assignment is nondeterministic
case class Modify(pat: AsgnPat, hp: Either[Term, Unit]) extends Statement
// Introduces a line label [[st]]. Terms f@st (likewise formulas) are then equal to the value of f at the location of
// [[Label(st)]]. Labels are globally scoped with forward and backward reference, but references must be acyclic
// for well-definedness
// @TODO: Implement
case class Label(st: TimeIdent) extends Statement
// Note checks forward [[proof]] and stores the result in proof-variable [[x]]
case class Note(x: Ident, proof: ProofTerm) extends Statement
// Introduces a lexically-scoped defined function [[x]] with arguments [[args]] and body [[e]]. References to [[args]]
// in [[e]] are resolved by substituting parameters at application sites. All others take their value according to the
// definition site of the function. Scope is lexical and functions must not be recursive for soundness.
case class LetFun(x: Ident, args: List[Ident], e: Expression) extends Statement
// Unifies expression [[e]] with pattern [[pat]], binding free term and formula variables of [[pat]]
case class Match(pat: Expression, e: Expression) extends Statement
// Sequential composition of elements of [[ss]]
case class Block(ss: Statements) extends Statement
// @TODO: add case-analysis with arguments, add proof variable binding
// Pattern formulas must form a constructively-exhaustive case analysis.
// In each branch, assume the pattern holds and prove the branch statement
// the conclusion is the disjunction of branches
case class Switch(pats: List[(Expression, Statement)]) extends Statement
// Execute either branch of a program nondeterministically, with corresponding proofs
case class BoxChoice(left: Statement, right: Statement) extends Statement
// x is a pattern
// Repeat body statement [[ss]] so long as [[j]] holds, with hypotheses in pattern [[x]]
case class While(x: Expression, j: Formula, ss: Statement) extends Statement
// Repeat [[s]] nondeterministically any number of times
case class BoxLoop(s: Statement) extends Statement
// Statement [[s]] is introduced for use in the proof but is not exported in the conclusion.
// For example, Ghost(Modify(_)) is a discrete ghost assignment
// @TODO: Resolve scope-escaping issues
case class Ghost(ss: Statement) extends Statement
// Inverse-ghost of statement [[s]], i.e., program of [[ss]] is part of the conclusion but not relevant to the proof.
// For example, InverseGhost(Assume(_)) indicates a Demonic test which is never used in the proof
case class InverseGhost(ss: Statement) extends Statement
// Debugging functionality: print [[msg]] with proof context
case class PrintGoal(msg: String) extends Statement
// Proof of differential equation, either angelic or demonic.
case class ProveODE(ds: DiffStatement, dc: DomainStatement) extends Statement //de: DifferentialProgram
// Debugging feature. Equivalent to "now" in all respects, annotated with the fact that it was once "was"
// before transformation by the proof checker
case class Was(now: Statement, was: Statement) extends Statement

// Proof steps regarding the differential program, such as ghosts and inverse ghosts used in solutions.
sealed trait DiffStatement extends ASTNode
// Specifies a single ODE being proved
case class AtomicODEStatement(dp: AtomicODE) extends DiffStatement
// Corresponding proofs for each conjunct of differential product
case class DiffProductStatement(l: DiffStatement, r: DiffStatement) extends DiffStatement
// Proof for ghost ODE introduced for sake of proof but not in conclusion
case class DiffGhostStatement(ds: DiffStatement) extends DiffStatement
// Proof for inverse ghost ODE which appears in conclusion but not proof. Used in solution reasoning.
case class InverseDiffGhostStatement(ds: DiffStatement) extends DiffStatement

//Proof steps regarding the domain, for example differential cuts and weakening of domain constraints.
// Angelic solutions require witnesses for duration, also given here
sealed trait DomainStatement extends ASTNode
// x is formula pattern in assume and assert
// Introduces assumption in domain, i.e., a domain formula which appears in the conclusion and can be accessed
// by differential weakening
case class DomAssume(x: Expression, f:Formula) extends DomainStatement
// Differential assertion which is proved with differential cut and then possibly used in proof
case class DomAssert(x: Expression, f:Formula, child: Method) extends DomainStatement
// Distinct from "differential weakening" rule, meaning a domain constraint which is in the conclusion but not the
// proof, which is weakened before continuing prof
case class DomWeak(dc: DomainStatement) extends DomainStatement
// Assignment to a variable. Only allowable use is to specify the duration of an angelic solution
case class DomModify(x: AsgnPat, hp: Assign) extends DomainStatement
// Conjunction of domain constraints with proofs for each conjunct
case class DomAnd(l: DomainStatement, r: DomainStatement) extends DomainStatement

object Context {
  def empty: Context = Context(Set())
}

// Structured context for checking Kaisar proofs
// @TODO: Implement the rest
case class Context (proofVars: Map[String, Formula]) {
  // Base name used for fresh variables generated during proof when no better variable name is available.
  val ghostVar: String = "ghost"
  // Extend context with a named assumption
  def add(ident: String, f: Formula): Context = Context(proofVars.+((ident, f)))

  // A proof variable name which is not bound in the context.
  def fresh: String = {
    var i = 0
    while(proofVars.contains(ghostVar + i)) {
      i = i + 1
    }
    ghostVar + i
  }

  // Define the next gHost variable to be f
  def ghost(f: Formula): Context = add(fresh, f)
  // Contents of context
  def toList: List[(String, Formula)] = proofVars.toList
}