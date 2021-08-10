package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BRANCH_COMBINATOR, BelleParser, BellePrettyPrinter, SEQ_COMBINATOR}
import edu.cmu.cs.ls.keymaerax.hydra.TacticExtractionErrors.TacticExtractionError
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Location, Region}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.util.Try

trait TraceToTacticConverter {
  def getTacticString(tree: ProofTree): (String, Map[Location, ProofTreeNode]) = getTacticString(tree.root, "")
  def getTacticString(node: ProofTreeNode, indent: String): (String, Map[Location, ProofTreeNode])
}

class VerboseTraceToTacticConverter(defs: Declaration) extends TraceToTacticConverter {
  private val INDENT_INCREMENT = "  "

  /** Tactic definitions from the tactic script (if any). */
  private val tacticDefs = scala.collection.mutable.Map.empty[String, BelleExpr]

  private def makeLocNodeMap(maker: String, node: ProofTreeNode): Map[Location, ProofTreeNode] = {
    //nil: proof state before = proof state after
    if (node.children.isEmpty) Map[Location, ProofTreeNode](Region(0, 0, 0, maker.length) -> node)
    //any other tactic: proof state after maker
    else Map[Location, ProofTreeNode](node.children.map(n => Region(0, 0, 0, maker.length) -> n):_*)
  }

  def getTacticString(node: ProofTreeNode, indent: String): (String, Map[Location, ProofTreeNode]) = {
    assert(!node.children.contains(node), "A node should not be its own child.")
    val (nodeMaker, nodeMakerLoc) = tacticStringAt(node) match {
      case (nm, Some(DefTactic(name, t))) =>
        tacticDefs(name) = t
        (nm, makeLocNodeMap(nm, node))
      case (nm, _) => (nm, makeLocNodeMap(nm, node))
    }
    val subgoalTactics = node.children.map(getTacticString(_, indent + (if (node.children.size <= 1) "" else INDENT_INCREMENT)))

    //@note expensive: labels are temporary, need to rerun tactic to create labels
    val labels = if (node.children.size > 1) {
      node.goal.map(s => BelleProvable(ProvableSig.startProof(s), None, defs)) match {
        case Some(p) =>
          node.children.headOption.flatMap(_.maker.map(m => tacticDefs.getOrElse(m, BelleParser.parseWithInvGen(m, None, defs)))) match {
            case Some(t) =>
              LazySequentialInterpreter()(t, p) match {
                case BelleProvable(_, Some(labels), _) => labels
                case _ => Nil
              }
            case None =>
              Nil
          }
      }
    } else Nil

    if (subgoalTactics.isEmpty) (indent + nodeMaker, shift(nodeMakerLoc, 0, indent.length))
    else if (subgoalTactics.size == 1) sequentialTactic((nodeMaker, nodeMakerLoc), subgoalTactics.head, indent)
    else if (subgoalTactics.size == labels.size) sequentialTactic((nodeMaker, nodeMakerLoc), {
        val (lines, locs) = subgoalTactics.zip(minimize(labels)).foldLeft[(List[String], Map[Location, ProofTreeNode])]((List.empty, Map.empty))({
          case ((rtext, rloc), ((ttext, tloc), label)) =>
            val indented = indent + INDENT_INCREMENT + "\"" + label.prettyString + "\":\n" + ttext.linesWithSeparators.map(INDENT_INCREMENT + _).mkString("")
            (rtext :+ indented, rloc ++ shift(tloc, 2*rtext.length + 1, (indent + INDENT_INCREMENT).length))
        })
        (lines.mkString(",\n") + "\n" + indent + ")", locs)
      },
      indent, SEQ_COMBINATOR.img + " " + BRANCH_COMBINATOR.img + "(")
    else sequentialTactic((nodeMaker, nodeMakerLoc), {
        val (lines, locs) = subgoalTactics.foldLeft[(List[String], Map[Location, ProofTreeNode])](List.empty, Map.empty)({
          case ((rtext, rloc), (ttext, tloc)) =>
            (rtext :+ ttext, rloc ++ shift(tloc, rtext.length, 0))
        })
      (lines.mkString(",\n") + "\n" + indent + ")", locs)
      },
      indent, SEQ_COMBINATOR.img + " " + BRANCH_COMBINATOR.img + "(")
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

  /** Shifts the location by `lines` and `columns`. */
  private def shift(loc: Map[Location, ProofTreeNode], lines: Int, columns: Int): Map[Location, ProofTreeNode] =
    loc.map({ case (l: Region, n) => (Region(l.line+lines, l.column+columns, l.endLine+lines, l.endColumn+columns), n) })

  /** Composes `ts1` and `ts2` sequentially, trims `ts1` and single-line `ts2` before composing them. */
  private def sequentialTactic(ts1: (String, Map[Location, ProofTreeNode]),
                               ts2: (String, Map[Location, ProofTreeNode]),
                               indent: String, sep: String = SEQ_COMBINATOR.img): (String, Map[Location, ProofTreeNode]) = {
    val (ts1t, ts2t) = if (ts2._1.lines.length <= 1) (ts1._1.trim, ts2._1.trim) else (ts1._1.trim, ts2._1.stripPrefix(indent))
    (ts1t, ts2t) match {
      /* todo adapt locations */
      case ("nil", _) | ("skip", _)=> (indent + ts2t, shift(ts2._2, 0, indent.length))
      case (_, "nil") | (_, "skip") => (indent + ts1t, shift(ts1._2, 0, indent.length))
      case ("" | "()", "" | "()") => ("", Map.empty)
      case (_, "" | "()") => (indent + ts1t, shift(ts1._2, 0, indent.length))
      case ("" | "()", _) => (indent + ts2t, shift(ts2._2, 0, indent.length))
      case _ => (indent + ts1t + sep + "\n" + indent + ts2t,
        shift(ts1._2, 0, indent.length) ++ shift(ts2._2, ts1t.lines.length, indent.length))
    }
  }

  /** Returns a copy of `pos` with index 0. */
  private def firstInSuccOrAnte(pos: Position): Position =
    if (pos.isAnte) AntePosition.base0(0, pos.inExpr) else SuccPosition.base0(0, pos.inExpr)

  /** Converts fixed position locators into search locators. */
  private def convertLocator(loc: PositionLocator, node: ProofTreeNode): PositionLocator = loc match {
    case Fixed(pos, None, _) => node.goal.flatMap(_.sub(pos.top)) match {
      case Some(e) => Find(0, Some(e), firstInSuccOrAnte(pos), exact=true, defs)
      case None => throw TacticExtractionError("Recorded position " + pos.prettyString + " does not exist in " +
        node.localProvable.subgoals.head.prettyString)
    }
    case Fixed(pos, Some(f), exact) => Find(0, Some(f), firstInSuccOrAnte(pos), exact, defs)
    case Find(goal, None, start, exact, _) =>
      val childGoal = node.children.headOption.flatMap(_.goal)
      val affected =
        if (start.isAnte) node.goal.map(_.ante.filterNot(childGoal.map(_.ante).getOrElse(IndexedSeq.empty).toSet).toList)
        else node.goal.map(_.succ.filterNot(childGoal.map(_.succ).getOrElse(IndexedSeq.empty).toSet).toList)
      affected match {
        case Some(e :: Nil) => Find(goal, Some(e), start, exact, defs)
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
          case Some(t: AppliedPositionTactic) => (BellePrettyPrinter(convertLocator(t, node)), Some(t))
          case Some(t: AppliedDependentPositionTactic) => (BellePrettyPrinter(convertLocator(t, node)), Some(t))
          case Some(t: AppliedDependentPositionTacticWithAppliedInput) => (BellePrettyPrinter(convertLocator(t, node)), Some(t))
          case Some(using@Using(es, t)) => (BellePrettyPrinter(Using(es, convertLocator(t, node))), Some(using))
          case Some(t) => (BellePrettyPrinter(convertLocator(t, node)), Some(t))
          case _ => (m, None)
        }
    }
  }

  /** Converts fixed positions into searchy locators. */
  private def convertLocator(tactic: BelleExpr, node: ProofTreeNode): BelleExpr = tactic match {
    case t@AppliedPositionTactic(_, l) => t.copy(locator = convertLocator(l, node))
    case t: AppliedDependentPositionTactic => new AppliedDependentPositionTactic(t.pt, convertLocator(t.locator, node))
    case t: AppliedDependentPositionTacticWithAppliedInput =>
      new AppliedDependentPositionTacticWithAppliedInput(t.pt, convertLocator(t.locator, node))
    case t => t
  }
}

/** A verbatim trace to tactic converter whose tactics are as recorded in the database. */
class VerbatimTraceToTacticConverter extends TraceToTacticConverter {

  def getTacticString(node: ProofTreeNode, indent: String): (String, Map[Location, ProofTreeNode]) = {
    assert(!node.children.contains(node), "A node should not be its own child.")
    val thisTactic = tacticStringAt(node)
    val subgoals = node.children.map(getTacticString(_, indent + (if (node.children.size <= 1) "" else "  ")))

    //@todo does pretty-printing
    if (subgoals.isEmpty) (thisTactic, Map.empty)
    else if (subgoals.size == 1) (sequentialTactic(thisTactic, subgoals.head._1), Map.empty)
    else (sequentialTactic(thisTactic, BRANCH_COMBINATOR.img + "(\n" + indent + subgoals.map(_._1).mkString(",\n" + indent) + "\n" + indent + ")"), Map.empty)
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

