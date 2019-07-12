package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, NamedTactic, SequentType, USubstPatternTactic}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import BelleLabels._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction

import scala.collection.immutable.IndexedSeq
import scala.collection.mutable.ListBuffer

/**
  * Implementation: some dL tactics using substitution tactics.
  * Created by nfulton on 11/3/15.
  */
private object DLBySubst {

  private[btactics] lazy val monb2 = byUS("[] monotone 2")

  /** whether games are currently allowed */
  private[this] val isGame: Boolean = try {Dual(AssignAny(Variable("x"))); true} catch {case ignore: IllegalArgumentException => false }

  /** @see [[HilbertCalculus.G]] */
  lazy val G: BelleExpr = {
    val pattern = SequentType(Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};]p_(||)".asFormula)))
    //@todo ru.getRenamingTactic should be trivial so can be optimized away with a corresponding assert
    if (false && isGame) //@note true changes the shape maybe?
      USubstPatternTactic(
        (pattern, (ru:RenUSubst) =>
          cut(ru.substitution.usubst("[a_;]true".asFormula)) <(
            ru.getRenamingTactic & TactixLibrary.by("[] monotone 2", ru.substitution.usubst ++ USubst(
              SubstitutionPair(UnitPredicational("q_", AnyArg), True) :: Nil
            )) &
              hideL(-1, True)
            ,
            hide(1) & boxTrue(1)
            ))::Nil)
    else
      USubstPatternTactic(
        (pattern, (ru:RenUSubst) => {
          Predef.assert(ru.getRenamingTactic == ident, "no renaming for Goedel")
          //ru.getRenamingTactic & by("Goedel", ru.substitution.usubst)
          TactixLibrary.by("Goedel", ru.usubst)
        })::Nil
    )
  }

  /** @see [[TactixLibrary.abstractionb]] */
  def abstractionb: DependentPositionTactic = new DependentPositionTactic("GV") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(!pos.isAnte, "Abstraction only in succedent")
        sequent.at(pos) match {
          case (ctx, b@Box(prg, phi)) =>
            val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
            val diffies = vars.filter(v => v.isInstanceOf[DifferentialSymbol])
            if (diffies.nonEmpty) throw new IllegalArgumentException("abstractionb: found differential symbols " + diffies + " in " + b + "\nFirst handle those")
            val qPhi =
              if (vars.isEmpty) phi
              else
              //@todo code quality needs improved
              //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
                vars.filter(v => v.isInstanceOf[BaseVariable]).map(v => v.asInstanceOf[NamedSymbol]).
                  to[scala.collection.immutable.SortedSet].
                  foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))

            cut(Imply(ctx(qPhi), ctx(b))) <(
              /* use */ implyL('Llast) <(hideR(pos.topLevel) /* result remains open */ , closeIdWith('Llast)),
              /* show */ cohide('Rlast) & CMon(pos.inExpr) & implyR(1) &
              assertT(1, 1) & assertT(s => s.ante.head == qPhi && s.succ.head == b, s"Formula $qPhi and/or $b are not in the expected positions in abstractionb") &
              topAbstraction(1) & closeId
              )
        }
      }
    }
  }

  /** Automated abstraction checks to not lose information from tests and evolution domain constraints before it abstracts. */
  def autoabstractionb: DependentPositionTactic = "autoabstractionb" by ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(prg, fml)) =>
        val fv = StaticSemantics.freeVars(fml)
        val bv = StaticSemantics.boundVars(prg)
        if (!bv.intersect(fv).isEmpty) throw new BelleFriendlyUserMessage("Abstraction would lose information from program")
        val fmls: ListBuffer[Formula] = ListBuffer.empty
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
            case Test(q) if q != True => fmls.append(q); Left(Some(ExpressionTraversal.stop))
            case ODESystem(_, q) if q != True => fmls.append(q); Left(Some(ExpressionTraversal.stop))
            case _ => Left(None)
          }
        }, prg)
        if (fmls.isEmpty) abstractionb(pos)
        else throw new BelleFriendlyUserMessage("Abstraction would lose information from tests and/or evolution domain constraints")
      case e => throw BelleTacticFailure("Inapplicable tactic: expected formula of the shape [a;]p but got " +
        e.map(_.prettyString) + " at position " + pos.prettyString + " in sequent " + seq.prettyString)
    }
  })

  /**
    * Introduces a self assignment [x:=x;]p(||) in front of p(||).
    *
    * @param x The self-assigned variable.
    */
  def stutter(x: Variable): DependentPositionTactic = "stutter" byWithInput (x, (pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (ctx, f: Formula) =>
      val (hidePos, commute) = if (pos.isAnte) (SuccPosition.base0(sequent.succ.size), commuteEquivR(1)) else (pos.topLevel, skip)
      cutLR(ctx(Box(Assign(x, x), f)))(pos) <(
        skip,
        cohide(hidePos) & equivifyR(1) & commute & CE(pos.inExpr) & byUS("[:=] self assign") & done
      )
  })

  /** Top-level abstraction: basis for abstraction tactic */
  private def topAbstraction: DependentPositionTactic = new DependentPositionTactic("Top-level abstraction") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(!pos.isAnte, "Abstraction only in succedent")
        sequent.sub(pos) match {
          case Some(b@Box(prg, phi)) =>
            val vars: scala.collection.immutable.SortedSet[Variable] = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.
              //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
              filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable]).to[scala.collection.immutable.SortedSet](
                //@note provide canBuildFrom and ordering because Scala implicit conversions won't compile
                scala.collection.immutable.SortedSet.canBuildFrom(new Ordering[Variable] {
                  override def compare(x: Variable, y: Variable): Int = x.compare(y)
                }))

            val qPhi = if (vars.isEmpty) phi else vars.foldRight(phi)((v, f) => Forall(v :: Nil, f))

            val diffRenameStep: DependentPositionTactic = "diffRenameStep" by ((pos: Position, sequent: Sequent) => sequent(AntePos(0)) match {
                case Equal(x: Variable, x0: Variable) if sequent(AntePos(sequent.ante.size - 1)) == phi =>
                  stutter(x0)(pos) & ProofRuleTactics.boundRenaming(x0, x)(pos.topLevel) & DebuggingTactics.print("Zee") &
                    eqR2L(-1)(pos.topLevel) & useAt("[:=] self assign")(pos.topLevel) & hide(-1)
                case _ => throw new ProverException("Expected sequent of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
              })

            val diffRename: DependentPositionTactic = "diffRename" by ((pos: Position, sequent: Sequent) => {
              //@note allL may introduce equations of the form x=x_0, but not necessarily for all variables
              if (sequent.ante.size == 1 && sequent.succ.size == 1 && sequent.ante.head == sequent.succ.head) ident
              else if (sequent.ante.size <= 1 + vars.size && sequent.succ.size == 1) sequent(AntePos(0)) match {
                case Equal(_, _) if sequent(AntePos(sequent.ante.size - 1)) == phi => diffRenameStep(pos)*(sequent.ante.size - 1)
                case _ => throw new ProverException("Expected sequent of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
              }
              else throw new ProverException("Expected sequent either of the form p(x) |- p(x)\n or of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
            })

            cut(Imply(qPhi, Box(prg, qPhi))) <(
              /* use */ (implyL('Llast) <(
                hideR(pos.topLevel) partial /* result */,
                cohide2(AntePosition(sequent.ante.length + 1), pos.topLevel) &
                  assertT(1, 1) & assertE(Box(prg, qPhi), "abstractionb: quantified box")('Llast) &
                  assertE(b, "abstractionb: original box")('Rlast) & ?(monb) &
                  assertT(1, 1) & assertE(qPhi, "abstractionb: quantified predicate")('Llast) &
                  assertE(phi, "abstractionb: original predicate")('Rlast) & (allL('Llast)*vars.size) &
                  diffRename(1) &
                  assertT(1, 1) & assertT(s => s.ante.head match {
                    case Forall(_, _) => phi match {
                      case Forall(_, _) => true
                      case _ => false
                    }
                    case _ => true
                  }, "abstractionb: foralls must match") & closeId
                )),
              /* show */ hideR(pos.topLevel) & implyR('Rlast) & V('Rlast) & closeIdWith('Llast)
            )
        }
      }
    }
  }

    /**
    * Equality assignment to a fresh variable.
    * Always introduces universal quantifier, which is already skolemized if applied at top-level in the
    * succedent; quantifier remains unhandled in the antecedent and in non-top-level context.
    *
    * @example{{{
    *    x_0=x+1 |- [{x_0:=x_0+1;}*]x_0>0
    *    ----------------------------------assignEquality(1)
    *        |- [x:=x+1;][{x:=x+1;}*]x>0
    * }}}
    * @example{{{
    *    \\forall x_0 (x_0=x+1 -> [{x_0:=x_0+1;}*]x_0>0) |-
    *    --------------------------------------------------- assignEquality(-1)
    *                 [x:=x+1;][{x:=x+1;}*]x>0 |-
    * }}}
    * @example Other uses of the variable in the context remain unchanged.
    * {{{
    *    x=2 |- [y:=2;]\\forall x_0 (x_0=x+1 -> [{x_0:=x_0+1;}*]x_0>0)
    *    -------------------------------------------------------------- assignEquational(1, 1::Nil)
    *    x=2   |- [y:=2;][x:=x+1;][{x:=x+1;}*]x>0
    * }}}
    * @author Andre Platzer
    * @incontext
    */
  lazy val assignEquality: DependentPositionTactic = "assignEquality" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    //@note have already failed assigning directly so grab fresh name index otherwise
    // [x:=f(x)]P(x)
    case Some(fml@Box(Assign(x, t), p)) =>
      val y = TacticHelper.freshNamedSymbol(x, sequent)
      ProofRuleTactics.boundRenaming(x, y)(pos) &
      useAt("[:=] assign equality")(pos) &
      ProofRuleTactics.uniformRenaming(y, x) &
      (if (pos.isTopLevel && pos.isSucc) allR(pos) & implyR(pos) else ident)
  })

  /** Equality assignment to a fresh variable. @see assignEquality @incontext */
  lazy val assigndEquality: DependentPositionTactic = "assigndEquality" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    //@note have already failed assigning directly so grab fresh name index otherwise
    // [x:=f(x)]P(x)
    case Some(fml@Diamond(Assign(x, t), p)) =>
      val y = TacticHelper.freshNamedSymbol(x, sequent)
      ProofRuleTactics.boundRenaming(x, y)(pos) &
        (if (pos.isSucc) useAt("<:=> assign equality all")(pos) else useAt("<:=> assign equality")(pos)) &
        ProofRuleTactics.uniformRenaming(y, x) &
        (if (pos.isTopLevel && pos.isSucc) allR(pos) & implyR(pos)
         else if (pos.isTopLevel && pos.isAnte) existsL(pos) & andL('Llast)
         else ident)
  })

  /** @see [[TactixLibrary.generalize()]]
   * @todo same for diamonds by the dual of K
   */
  def generalize(c: Formula, isGame: Boolean = false): DependentPositionTactic = {
    "MR" byWithInput(c, (pos: Position, sequent: Sequent) => sequent.at(pos) match {
      case (ctx, Box(a, p)) =>
        val ov = FormulaTools.argsOf("old", c)

        var freshOld: Variable = TacticHelper.freshNamedSymbol(Variable("old"), sequent)
        val ghosts: List[((Term, Variable), BelleExpr)] = ov.map(old => {
          val (ghost: Variable, ghostPos: Option[Position], nextCandidate) = TacticHelper.findSubst(old, freshOld, sequent)
          freshOld = nextCandidate
          (old -> ghost,
            ghostPos match {
              case None if pos.isTopLevel => discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquality(pos) &
                TactixLibrary.exhaustiveEqR2L(hide=false)('Llast)
              case Some(gp) if pos.isTopLevel => TactixLibrary.exhaustiveEqR2L(hide=false)(gp)
              case _ if !pos.isTopLevel => discreteGhost(old, Some(ghost))(pos)
            })
        }).toList
        val posIncrements = if (pos.isTopLevel) 0 else ghosts.size
        val afterGhostsPos = pos ++ PosInExpr(List.fill(posIncrements)(1))

        val oldifiedC = SubstitutionHelper.replaceFn("old", c, ghosts.map(_._1).toMap)
        val oldifiedA = ghosts.foldLeft(a)({case (prg, ((w, r), _)) => SubstitutionHelper.replaceFree(prg)(w, r) })
        val introduceGhosts = ghosts.map(_._2).reduceOption(_ & _).getOrElse(skip)

        val (q, useCleanup, showCleanup) = {
          val aBVs = StaticSemantics.boundVars(a)
          val constConjuncts =
            if (aBVs.isInfinite) Nil
            else sequent.ante.map(fml =>
              ghosts.foldLeft(fml)({ case (f, ((what, repl), _)) => SubstitutionHelper.replaceFree(f)(what, repl) })).
              flatMap(FormulaTools.conjuncts).
              filter(StaticSemantics.symbols(_).intersect(aBVs.toSet).isEmpty).toList
          (constConjuncts, isGame) match {
            case ((Nil, _) | (_, true)) => (oldifiedC, skip, implyR(1))
            case (consts, false) => (And(consts.reduceRight(And), oldifiedC),
                boxAnd(afterGhostsPos) &
                abstractionb(afterGhostsPos ++ PosInExpr(0 :: Nil)) &
                (if (afterGhostsPos.isTopLevel) andR(afterGhostsPos) & Idioms.<(prop & done, skip)
                else skip),
                implyR(1) & andL(-1)
            )
          }
        }
        introduceGhosts & cutR(ctx(Box(oldifiedA, q)))(afterGhostsPos.checkSucc.top) < (
          /* use */
          /*label(BranchLabels.genUse)*/ useCleanup,
          /* show */ cohide(afterGhostsPos.top) & CMon(afterGhostsPos.inExpr ++ 1) & showCleanup //& label(BranchLabels.genShow)
        )
    })
  }
  /** @see [[TactixLibrary.postCut()]]
   * @todo same for diamonds by the dual of K
   * @note Uses K modal modus ponens, which is unsound for hybrid games.
   */
  def postCut(C: Formula): DependentPositionTactic = useAt("K modal modus ponens &", PosInExpr(1::Nil),
    (us: Option[Subst]) => us.getOrElse(throw BelleUserGeneratedError("Unexpected missing substitution in postCut")) ++ RenUSubst(("p_(||)".asFormula, C)::Nil))

  private def constAnteConditions(sequent: Sequent, taboo: SetLattice[Variable]): IndexedSeq[Formula] = {
    sequent.ante.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
  }

  private def constSuccConditions(sequent: Sequent, taboo: SetLattice[Variable]): IndexedSeq[Formula] = {
    sequent.succ.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
  }

  /** @see [[TactixLibrary.loop]] */
  def loop(invariant: Formula, pre: BelleExpr = SaturateTactic(alphaRule)): DependentPositionWithAppliedInputTactic = "loop" byWithInput(invariant, (pos, sequent) => {
    require(pos.isTopLevel && pos.isSucc, "loop only at top-level in succedent, but got " + pos)

    val ov = FormulaTools.argsOf("old", invariant)
    val doloop = (ghosts: List[((Term, Variable), BelleExpr)]) => {
      val posIncrements = PosInExpr(List.fill(if (pos.isTopLevel) 0 else ghosts.size)(1))
      val oldified = SubstitutionHelper.replaceFn("old", invariant, ghosts.map(_._1).toMap)
      val afterGhostsPos = if (ghosts.nonEmpty) LastSucc(0, posIncrements) else Fixed(pos.topLevel ++ posIncrements)
      ghosts.map(_._2).reduceOption(_ & _).getOrElse(skip) &
        ("doLoop" byWithInput(oldified, (pos, sequent) => {
          sequent.sub(pos) match {
            case Some(b@Box(Loop(a), p)) =>
              if (!FormulaTools.dualFree(a)) loopRule(oldified)(pos)
              else {
                val abv = StaticSemantics(a).bv
                val constSuccs = (constSuccConditions(sequent, abv) :+ False).map(Not)
                val constAntes = constAnteConditions(sequent, abv)
                val consts = constAntes ++ constSuccs
                val q =
                  if (consts.size > 1) And(oldified, consts.reduceRight(And))
                  else if (consts.size == 1) And(oldified, consts.head)
                  else And(oldified, True)
                cutR(Box(Loop(a), q))(pos.checkSucc.top) & Idioms.<(
                  /* c */ useAt("I induction")(pos) & andR(pos) & Idioms.<(
                    andR(pos) & Idioms.<(
                      label(initCase),
                      (andR(pos) & Idioms.<(closeIdWith(pos), ident))*constAntes.size &
                        (andR(pos) & Idioms.<(notR(pos) & closeIdWith('Llast), ident))*(constSuccs.size-1) &
                        (if (constSuccs.nonEmpty) notR(pos) else skip) &
                        close & done),
                    cohide(pos) & G & implyR(1) & boxAnd(1) & andR(1) & Idioms.<(
                      (if (consts.nonEmpty) andL('Llast)*consts.size & hideL('Llast, Not(False)) & notL('Llast)*(constSuccs.size-1)
                       else andL('Llast) & hideL('Llast, True)) & label(indStep),
                      andL(-1) & hideL(-1, oldified) & V(1) & close(-1, 1) & done)
                  ),
                  /* c -> d */ cohide(pos) & CMon(pos.inExpr++1) & implyR(1) &
                    (if (consts.nonEmpty) andL('Llast)*consts.size & hideL('Llast, Not(False)) & notL('Llast)*(constSuccs.size-1)
                     else andL('Llast) & hideL('Llast, True)) & label(useCase)
                )
              }
          }}))(afterGhostsPos)
    }
    pre & discreteGhosts(ov, sequent, doloop)(pos)
  })

  /**
    * Loop induction wiping all context.
    * {{{
    *   init:        step:       use:
    *   G |- I, D    I |- [a]I   I |- p
    *   --------------------------------
    *   G |- [{a}*]p, D
    * }}}
    *
    * @param invariant The invariant.
    */

  def loopRule(invariant: Formula): DependentPositionWithAppliedInputTactic = "loopRule" byWithInput(invariant, (pos, sequent) => {
    //@todo maybe augment with constant conditions?
    require(pos.isTopLevel && pos.isSucc, "loopRule only at top-level in succedent, but got " + pos)
    require(sequent(pos) match { case Box(Loop(_),_)=>true case _=>false}, "only applicable for [a*]p(||)")
    //val alast = AntePosition(sequent.ante.length)
    cutR(invariant)(pos.checkSucc.top) <(
        ident & label(BelleLabels.initCase),
        cohide(pos) & implyR(1) & generalize(invariant, isGame = true)(1) <(
          byUS("ind induction") & label(BelleLabels.indStep)
          ,
          ident & label(BelleLabels.useCase)
        )
      )
  })

  /** @see [[TactixLibrary.throughout]] */
  def throughout(invariant: Formula, pre: BelleExpr = SaturateTactic(alphaRule)): DependentPositionWithAppliedInputTactic = "throughout" byWithInput(invariant, (pos, sequent) => {
    require(pos.isTopLevel && pos.isSucc, "throughout only at top-level in succedent, but got " + pos)
    lazy val split: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(Compose(_, _), _)) => composeb(pos) & generalize(invariant)(pos) & Idioms.<(skip, split(pos))
      case _ => skip
    })

    loop(invariant, pre)(pos) & Idioms.<(
      skip,
      skip,
      split(pos)
    )})

  /** [[TactixLibrary.con()]] */
  def con(v: Variable, variant: Formula, pre: BelleExpr = SaturateTactic(alphaRule)): DependentPositionWithAppliedInputTactic = "con" byWithInputs(v::variant::Nil, (pos, sequent) => {
    require(pos.isTopLevel && pos.isSucc, "con only at top-level in succedent, but got " + pos)
    require(sequent(pos) match { case Diamond(Loop(_), _) => true case _ => false }, "only applicable for <a*>p(||)")

    pre & ("doCon" byWithInput(variant, (pp, seq) => {
      seq.sub(pp) match {
        case Some(Diamond(prg: Loop, _)) if !FormulaTools.dualFree(prg) => conRule(v, variant)(pos)
        case Some(d@Diamond(prg@Loop(a), p)) if  FormulaTools.dualFree(prg) =>
          val ur = URename(Variable("x_",None,Real), v)
          val abv = StaticSemantics(a).bv
          val consts = constAnteConditions(seq, abv)
          val q =
            if (consts.size > 1) And(ur(variant), consts.reduceRight(And))
            else if (consts.size == 1) And(ur(variant), consts.head)
            else And(ur(variant), True)

          val x1 = Variable(ur.what.name, Some(ur.what.index.getOrElse(-1)+1)) //@note avoid clash with x_ when assignd uses assigndEquality
          val x2 = Variable(x1.name, Some(x1.index.get+1))          //@note result after assigndEquality
          val v0 = Variable(v.name, Some(v.index.getOrElse(-1)+1))  //@note want v__0 in result instead of x2

          def closeConsts(pos: Position) = andR(pos) <(skip, onAll(andR(pos) <(closeId, skip))*(consts.size-1) & close)
          val splitConsts = if (consts.nonEmpty) andL('Llast)*consts.size else useAt(DerivedAxioms.andTrue.fact)('Llast)

          val abvVars = abv.toSet[Variable].filter(_.isInstanceOf[BaseVariable]).toList
          def stutterABV(pos: Position) = abvVars.map(stutter(_)(pos)).reduceOption[BelleExpr](_&_).getOrElse(skip)
          def unstutterABV(pos: Position) = useAt("[:=] self assign")(pos)*abvVars.size

          cutR(Exists(ur.what :: Nil, q))(pp.checkSucc.top) <(
            stutter(ur.what)(pos ++ PosInExpr(0::0::Nil)) &
            useAt(DerivedAxioms.partialVacuousExistsAxiom)(pos) & closeConsts(pos) &
            assignb(pos ++ PosInExpr(0::Nil)) & uniformRename(ur) & label(BelleLabels.initCase)
            ,
            //@todo adapt to "con convergence flat" and its modified branch order
            cohide(pp) & implyR(1) & existsL(-1) & byUS("con convergence flat") <(
              existsL('Llast) & andL('Llast) & splitConsts & uniformRename(ur) & label(BelleLabels.useCase)
              ,
              stutter(ur.what)(1, 1::1::0::Nil) &
              useAt("<> partial vacuous", PosInExpr(1::Nil))(1, 1::Nil) &
              assignb(1, 1::0::1::Nil) &
              stutterABV(SuccPosition.base0(0, PosInExpr(1::0::Nil))) &
              useAt("<> partial vacuous", PosInExpr(1::Nil))(1) &
              unstutterABV(SuccPosition.base0(0, PosInExpr(0::1::Nil))) &
              splitConsts & closeConsts(SuccPos(0)) &
              (assignd(1, 1 :: Nil) & uniformRename(ur) |
                uniformRename(ur.what, x1) & assignd(1, 1 :: Nil) & boundRename(x1, v)(1, 1::Nil) & uniformRename(x2, v0)
                ) & label(BelleLabels.indStep)
            )
          )
      }
    }))(pos)
  })

  /**
    * Loop convergence wiping all context.
    * {{{
    *   init:                       use:                  step:
    *   G |- exists v. J(v), D    v<=0, J(v) |- p     v>0, J(v) |- <a>J(v-1)
    *   --------------------------------------------------------------------------
    *   G |- <{a}*>p, D
    * }}}
    * @param variant The variant property or convergence property in terms of new variable `v`.
    * @example The variant J(v) ~> (v = z) is specified as v=="v".asVariable, variant == "v = z".asFormula
    */
  def conRule(v: Variable, variant: Formula) = "conRule" byWithInput(variant, (pos, sequent) => {
    require(pos.isTopLevel && pos.isSucc, "conRule only at top-level in succedent, but got " + pos)
    require(sequent(pos) match { case Diamond(Loop(_), _) => true case _ => false }, "only applicable for <a*>p(||)")
    val ur = URename(Variable("x_",None,Real), v)

    cutR(Exists(ur.what ::Nil, ur(variant)))(pos.checkSucc.top) <(
      uniformRename(ur) & label(BelleLabels.initCase)
      ,
      cohide(pos) & implyR(1)
        & existsL(-1)
        & byUS("con convergence flat") <(
        existsL(-1) & andL(-1) & uniformRename(ur) & label(BelleLabels.useCase)
        ,
        assignd(1, 1 :: Nil) & uniformRename(ur) & label(BelleLabels.indStep)
        )
    )
  })

  /** @see [[TactixLibrary.discreteGhost()]] */
  def discreteGhost(t: Term, ghost: Option[Variable]): DependentPositionWithAppliedInputTactic = "discreteGhost" byWithInputs (
      ghost match { case Some(g) => List(t, g) case _ => List(t) }, (pos: Position, seq: Sequent) => {
    require(ghost match { case Some(g) => g != t case None => true }, "Expected ghost different from t, use stutter instead")
    seq.sub(pos) match {
      case Some(f: Formula) =>
        // check specified name, or construct a new name for the ghost variable if None
        def ghostV(f: Formula): Variable = ghost match {
          case Some(gv) => require(gv == t || (!StaticSemantics.symbols(f).contains(gv))); gv
          case None => t match {
            case v: Variable => TacticHelper.freshNamedSymbol(v, f)
            case _ => TacticHelper.freshNamedSymbol(Variable("ghost"), seq)
          }
        }
        val theGhost = ghostV(f)
        val theF = t match {
          //@note first two cases: backwards compatibility with diffSolve and others
          case _: Variable => f.replaceFree(t, DotTerm())
          case _ if StaticSemantics.boundVars(f).intersect(StaticSemantics.freeVars(t)).isEmpty => f.replaceFree(t, DotTerm())
          case _ => f //@note new: arbitrary term ghosts
        }

        val subst = (us: Option[Subst]) => RenUSubst(
          ("x_".asVariable, theGhost) ::
          ("f()".asTerm, t) ::
          ("p(.)".asFormula, theF) ::
          Nil
        )

        useAt("[:=] assign", PosInExpr(1::Nil), subst)(pos)
    }
  })

  /** Introduces ghost variables with a fresh name in `origSeq' for each of the terms `trms', before continuing with the
    * tactic produced by `cont`. */
  def discreteGhosts(trms: Set[Term], origSeq: Sequent,
                     cont: List[((Term, Variable), BelleExpr)] => BelleExpr): DependentPositionTactic = "ANON" by ((pos: Position, seq: Sequent) => {
    var freshOld: Variable = TacticHelper.freshNamedSymbol(Variable("old"), origSeq)
    val ghosts: List[((Term, Variable), BelleExpr)] = trms.map(old => {
      val (ghost: Variable, ghostPos: Option[Position], nextCandidate) = TacticHelper.findSubst(old, freshOld, origSeq)
      freshOld = nextCandidate
      (old -> ghost,
        ghostPos match {
          case None if pos.isTopLevel => discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquality(pos) &
            TactixLibrary.exhaustiveEqR2L(hide=false)('Llast)
          case Some(gp) if pos.isTopLevel => TactixLibrary.exhaustiveEqR2L(hide=false)(gp)
          case _ if !pos.isTopLevel => discreteGhost(old, Some(ghost))(pos)
        })
    }).toList
    cont(ghosts)
  })

  /**
   * Turns an existential quantifier into an assignment.
    *
    * @example{{{
   *         |- [t:=f;][x:=t;]x>=0
   *         -------------------------assignbExists(f)(1)
   *         |- \exists t [x:=t;]x>=0
   * }}}
   * @param f The right-hand side term of the assignment chosen as a witness for the existential quantifier.
   * @return The tactic.
   */
  def assignbExists(f: Term): DependentPositionTactic = "assignbExistsRule" byWithInput (f, (pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Exists(vars, p)) =>
      require(vars.size == 1, "Cannot handle existential lists")
      val subst = (s: Option[Subst]) =>
        s.getOrElse(throw BelleUnsupportedFailure("Expected unification in assignbExists")) ++ RenUSubst(USubst("f_()".asTerm ~> f :: Nil))
      useAt("[:=] assign exists", PosInExpr(1::Nil), subst)(pos)
  })

  /**
    * Turns a universal quantifier into an assignment.
    *
    * @example{{{
    *         [t:=f;][x:=t;]x>=0 |-
    *         -------------------------assignbAll(f)(-1)
    *         \forall t [x:=t;]x>=0 |-
    * }}}
    * @param f The right-hand side term of the assignment chosen as a witness for the universal quantifier.
    * @return The tactic.
    */
  def assignbAll(f: Term): DependentPositionTactic = "[:=] assign all" byWithInput (f, (pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Forall(vars, p)) =>
      require(vars.size == 1, "Cannot handle universal lists")
      val subst = (s: Option[Subst]) =>
        s.getOrElse(throw BelleUnsupportedFailure("Expected unification in assignbExists")) ++ RenUSubst(USubst("f_()".asTerm ~> f :: Nil))
      useAt("[:=] assign all", PosInExpr(0::Nil), subst)(pos)
  })
}
