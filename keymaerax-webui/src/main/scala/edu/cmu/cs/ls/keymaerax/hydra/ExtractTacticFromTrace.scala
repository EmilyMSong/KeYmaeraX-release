package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BRANCH_COMBINATOR, BelleParser, BellePrettyPrinter, SEQ_COMBINATOR}
import edu.cmu.cs.ls.keymaerax.hydra.TacticExtractionErrors.TacticExtractionError
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.util.Try

trait TraceToTacticConverter {
  def getTacticString(tree: ProofTree): String = getTacticString(tree.root, "")
  def getTacticString(node: ProofTreeNode, indent: String): String
}

class VerboseTraceToTacticConverter extends TraceToTacticConverter {
  private val INDENT_INCREMENT = "  "

  /** Tactic definitions from the tactic script (if any). */
  private val tacticDefs = scala.collection.mutable.Map.empty[String, BelleExpr]

  def getTacticString(node: ProofTreeNode, indent: String): String = {
    assert(!node.children.contains(node), "A node should not be its own child.")
    val nodeMaker = tacticStringAt(node) match {
      case (nm, Some(DefTactic(name, t))) =>
        tacticDefs(name) = t
        nm
      case (nm, _) => nm
    }
    val subgoalTactics = node.children.map(getTacticString(_, indent + (if (node.children.size <= 1) "" else INDENT_INCREMENT)))

    //@note expensive: labels are temporary, need to rerun tactic to create labels
    val labels = if (node.children.size > 1) {
      node.goal.map(s => BelleProvable(ProvableSig.startProof(s))) match {
        case Some(p) =>
          node.children.headOption.flatMap(_.maker.map(m => tacticDefs.getOrElse(m, BelleParser(m)))) match {
            case Some(t) =>
              LazySequentialInterpreter()(t, p) match {
                case BelleProvable(_, Some(labels)) => labels
                case _ => Nil
              }
            case None =>
              Nil
          }
      }
    } else Nil

    if (subgoalTactics.isEmpty) indent + nodeMaker
    else if (subgoalTactics.size == 1) indent + sequentialTactic(nodeMaker, subgoalTactics.head, indent)
    else sequentialTactic(nodeMaker,
      subgoalTactics.zip(minimize(labels)).map({ case (t, l) => indent + "\"" + l.prettyString + "\":\n" + indent + "  " + t }).mkString(",\n" + indent + "  ") +
      "\n" + indent + ")", indent, SEQ_COMBINATOR.img + " " + BRANCH_COMBINATOR.img + "(")
  }

  /** Returns the unique tails of labels `l` as labels. */
  @tailrec
  private def minimize(l: List[BelleLabel], depth: Int = 1): List[BelleLabel] = {
    if (depth > l.map(_.components.size).max) throw new IllegalArgumentException("Duplicate label in " +
      l.map(_.prettyString).mkString("::") + "\n(verbose) " + l.map(_.toString).mkString("::"))
    val projectedLabels = l.map(_.components.takeRight(depth).map(_.label))
    if (projectedLabels.size == projectedLabels.toSet.size) projectedLabels.map(l =>
      l.tail.foldLeft[BelleLabel](BelleTopLevelLabel(l.head))(BelleSubLabel))
    else minimize(l, depth + 1)
  }

  private def sequentialTactic(ts1: String, ts2: String, indent: String, sep: String = SEQ_COMBINATOR.img): String = {
    val (ts1t, ts2t) = (ts1.trim, ts2.trim)
    (ts1t, ts2t) match {
      case ("nil", _) | ("skip", _)=> ts2t
      case (_, "nil") | (_, "skip") => ts1t
      case ("" | "()", "" | "()") => ""
      case (_, "" | "()") => ts1t
      case ("" | "()", _) => ts2t
      case _ => ts1t + sep + "\n" + indent + ts2t
    }
  }

  /** Returns a copy of `pos` with index 0. */
  private def firstInSuccOrAnte(pos: Position): Position =
    if (pos.isAnte) AntePosition.base0(0, pos.inExpr) else SuccPosition.base0(0, pos.inExpr)

  /** Converts fixed position locators into search locators. */
  private def convertLocator(loc: PositionLocator, node: ProofTreeNode): PositionLocator = loc match {
    case Fixed(pos, None, _) => node.goal.flatMap(_.sub(pos.top)) match {
      case Some(e) => Find(0, Some(e), firstInSuccOrAnte(pos), exact=true)
      case None => throw TacticExtractionError("Recorded position " + pos.prettyString + " does not exist in " +
        node.localProvable.subgoals.head.prettyString)
    }
    case Fixed(pos, Some(f), exact) => Find(0, Some(f), firstInSuccOrAnte(pos), exact)
    case Find(goal, None, start, exact) =>
      val childGoal = node.children.headOption.flatMap(_.goal)
      val affected =
        if (start.isAnte) node.goal.map(_.ante.filterNot(childGoal.map(_.ante).getOrElse(IndexedSeq.empty).toSet).toList)
        else node.goal.map(_.succ.filterNot(childGoal.map(_.succ).getOrElse(IndexedSeq.empty).toSet).toList)
      affected match {
        case Some(e :: Nil) => Find(goal, Some(e), start, exact)
        case _ => throw TacticExtractionError("Recorded position " + loc.prettyString + " does not exist in " + node.localProvable)
      }
    case _ => loc
  }

  //@note all children share the same maker
  private def tacticStringAt(node: ProofTreeNode): (String, Option[BelleExpr]) = node.children.headOption match {
    case None => ("nil", None)
    case Some(c) => c.maker match {
      case None => ("nil", None)
      case Some(m) =>
        if (BelleExpr.isInternal(m)) ("???", None) //@note internal tactics are not serializable (and should not be in the trace)
        else Try(BelleParser.parseWithTacticDefs(m, tacticDefs.toMap)).toOption match {
          case Some(t@AppliedPositionTactic(_, l)) =>
            (BellePrettyPrinter(t.copy(locator = convertLocator(l, node))), Some(t))
          case Some(t: AppliedDependentPositionTactic) =>
            (BellePrettyPrinter(new AppliedDependentPositionTactic(t.pt, convertLocator(t.locator, node))), Some(t))
          case Some(t: AppliedDependentPositionTacticWithAppliedInput) =>
            (BellePrettyPrinter(new AppliedDependentPositionTacticWithAppliedInput(t.pt, convertLocator(t.locator, node))), Some(t))
          case Some(t) => (BellePrettyPrinter(t), Some(t))
          case _ => (m, None)
        }
    }
  }
}

/** A legacy trace to tactic converter whose tactics are not verbose but unfortunately not robust either. */
@deprecated(since="4.9.4")
class LegacyTraceToTacticConverter extends TraceToTacticConverter {

  def getTacticString(node: ProofTreeNode, indent: String): String = {
    assert(!node.children.contains(node), "A node should not be its own child.")
    val thisTactic = tacticStringAt(node)
    val subgoals = node.children.map(getTacticString(_, indent + (if (node.children.size <= 1) "" else "  ")))

    //@todo does pretty-printing
    if (subgoals.isEmpty) thisTactic
    else if (subgoals.size == 1) sequentialTactic(thisTactic, subgoals.head)
    else sequentialTactic(thisTactic, BRANCH_COMBINATOR.img + "(\n" + indent + subgoals.mkString(",\n" + indent) + "\n" + indent + ")")
  }
  
  private def sequentialTactic(ts1: String, ts2: String): String = (ts1.trim(), ts2.trim()) match {
    case ("nil", _) | ("skip", _)=> ts2
    case (_, "nil") | (_, "skip") => ts1
    case ("" | "()", "" | "()") => ""
    case (_, "" | "()") => ts1
    case ("" | "()", _) => ts2
    case _ => ts1 + " " + SEQ_COMBINATOR.img + " " + ts2
  }

  //@note all children share the same maker
  private def tacticStringAt(node: ProofTreeNode): String = node.children.headOption match {
    case None => "nil"
    case Some(c) => c.maker match {
      case None => "nil"
      case Some(m) =>
        if (BelleExpr.isInternal(m)) "???" //@note internal tactics are not serializable (and should not be in the trace)
        else m
    }
  }
}

object TacticExtractionErrors {
  class TacticExtractionError(message: String, cause: Option[Throwable]) extends Exception(message + {cause match {case Some(e) => ". Caused by: " + e.getMessage; case None => ""}})
  object TacticExtractionError {
    def apply(message: String, cause: Exception) = new TacticExtractionError(message, Some(cause))
    def apply(message: String, cause: Throwable) = new TacticExtractionError(message, Some(cause))
    def apply(message: String) = new TacticExtractionError(message, None)
  }
}

