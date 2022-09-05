package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BuiltInPositionTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{DerivationInfo, ProvableInfo}
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.ProofCheckException
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt._

object ProofTermChecker {
  def ruleToTactic(rule: Rule): BelleExpr = {
    rule match {
      case Close(ante, succ) => SequentCalculus.closeId(ante, succ)
      case CoHide2(ante, succ) => SequentCalculus.cohide2(ante, succ)
      case CutRight(fml, succ) => SequentCalculus.cutR(fml)(succ)
      case ImplyRight(succ) => SequentCalculus.implyR(succ)
      case AndRight(succ) => SequentCalculus.andR(succ)
      case CoHideRight(succ) => SequentCalculus.cohideR(succ)
      case CommuteEquivRight(succ) => SequentCalculus.commuteEquivR(succ)
      case EquivifyRight(succ) => SequentCalculus.equivifyR(succ)
      case EquivRight(succ) => SequentCalculus.equivR(succ)
      case NotRight(succ) => SequentCalculus.notR(succ)
      case CloseTrue(succ) => ProofRuleTactics.closeTrue(succ)
      case HideRight(succ) => SequentCalculus.hideR(succ)
      case OrRight(succ) => SequentCalculus.orR(succ)

      case OrLeft(ante) => SequentCalculus.orL(ante)
      case AndLeft(ante) => SequentCalculus.andL(ante)
      case HideLeft(ante) => SequentCalculus.hideL(ante)
      case CutLeft(fml, ante) => SequentCalculus.cutL(fml)(ante)
      case ImplyLeft(ante) => SequentCalculus.implyL(ante)
      case NotLeft(ante) => SequentCalculus.notL(ante)
      case EquivLeft(ante) => SequentCalculus.equivL(ante)
      case CloseFalse(ante) => ProofRuleTactics.closeFalse(ante)

      case BoundRenaming(what, repl, seq: SeqPos) => ProofRuleTactics.boundRename(what, repl)(seq)
      case UniformRenaming(what, repl) => ProofRuleTactics.uniformRename(what, repl)
      case Skolemize(seq: SeqPos) => SequentCalculus.allR(seq)
      case Cut(fml) => SequentCalculus.cut(fml)

      case _ =>
        throw new Exception(s"ProofTermChecker.getTactic(...) is not completely implemented. Missing case: ${rule.name}") // @todo add cases as necessary
    }
  }

  def createBelleExpr(tac1: BelleExpr, tac2: BelleExpr, idx: Int, total: Int) = {
    if (total <= 1) tac1 & tac2
    else {
      val skips = Seq.fill(total)(TactixLibrary.skip).updated(idx, tac2)
      tac1 < (skips: _*)
    }
  }

  def translate(e: ProofTerm): BelleExpr = {
    val result : BelleExpr =
      e match {
        case FOLRConstant(f) => QE // & done
        case RuleApplication(child, rule, subgoal, total) => createBelleExpr(translate(child), ruleToTactic(rule), subgoal, total)
        case Sub(child, sub, i, total) => createBelleExpr(translate(child), translate(sub), i, total)
        case StartProof(goal) => TactixLibrary.skip
        // case RuleTerm(name) => QE //@todo update
        case AxiomTerm(axiomName) =>
          DerivationInfo(axiomName) match {
            case pi: ProvableInfo => UnifyUSCalculus.byUS(pi) // UnifyUSCalculus.useAt(pi)(1)
          }
        // case ForwardNewConsequenceTerm(child, con, rule) => translate(child) //@todo update
        // case ProlongationTerm(child, pro) => translate(child) //@todo update
        case URenameTerm(child, ren) => translate(child) // & UnifyUSCalculus.uniformRename(ren) // RenUSubst(ren)
        case UsubstProvableTerm(child, sub) => translate(child) & UnifyUSCalculus.US(sub) // UnifyUSCalculus.uniformSubstitute(sub)
        case NoProof => throw ProofCheckException("Tried to translate proof, but it has NoProof")
      }
    result
  }
}
