import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

/**
  * Tests the implementation of axiom schemas.
  *
  * @author Yong Kiam Tan
  */
class AxiomSchemaTests  extends TacticTestBase {

  "Vectorial DG" should "return 1D VDG" in {
    val vdg = Provable.vectorialDG(1)

    vdg._1 shouldBe 'proved
    vdg._2 shouldBe 'proved
    vdg._1.conclusion shouldBe "==> [{y__1'=g1(||),c{|y__1|}&q(|y__1|)}]y__1*y__1<=f_(|y__1|)->[{y__1'=g1(||),c{|y__1|}&q(|y__1|)}]p(|y__1|)->[{c{|y__1|}&q(|y__1|)}]p(|y__1|)".asSequent
    vdg._2.conclusion shouldBe "==> [{c{|y__1|}&q(|y__1|)}]p(|y__1|)->[{y__1'=g1(||),c{|y__1|}&q(|y__1|)}]p(|y__1|)".asSequent
  }

  it should "throw core exceptions on out-of-bounds dimension arguments" in {
    an[CoreException] should be thrownBy Provable.vectorialDG(0)
    an[CoreException] should be thrownBy Provable.vectorialDG(-1)
  }

  it should "return a 2D VDG" in {
    val vdg = Provable.vectorialDG(2)

    val y1 = Variable("y_",Some(1))
    val y2 = Variable("y_",Some(2))
    val except = Except(y1::y2:: Nil)
    val code = DifferentialProgramConst("c", except)
    val ppred = UnitPredicational("p", except)
    val qpred = UnitPredicational("q", except)
    val ffunc = UnitFunctional("f_",except,Real)
    val yode1 = AtomicODE(DifferentialSymbol(y1), UnitFunctional("g1",AnyArg,Real))
    val yode2 = AtomicODE(DifferentialSymbol(y2), UnitFunctional("g2",AnyArg,Real))

    val ghostode = ODESystem(DifferentialProduct(yode1,DifferentialProduct(yode2,code)),qpred)

    val f1 = Imply(Box(ghostode, LessEqual(Plus(Times(y1,y1),Times(y2,y2)),ffunc)),
      Imply(Box(ghostode, ppred), Box(ODESystem(code,qpred), ppred)))

    val f2 = Imply(Box(ODESystem(code,qpred), ppred), Box(ghostode, ppred))

    vdg._1 shouldBe 'proved
    vdg._2 shouldBe 'proved
    vdg._1.conclusion shouldBe Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(f1))
    vdg._2.conclusion shouldBe Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(f2))

    vdg._1.conclusion shouldBe "==> [{y__1'=g1(||),y__2'=g2(||),c{|y__1,y__2|}&q(|y__1,y__2|)}]y__1*y__1+y__2*y__2<=f_(|y__1,y__2|)->[{y__1'=g1(||),y__2'=g2(||),c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)->[{c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)".asSequent
    vdg._2.conclusion shouldBe "==> [{c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)->[{y__1'=g1(||),y__2'=g2(||),c{|y__1,y__2|}&q(|y__1,y__2|)}]p(|y__1,y__2|)".asSequent
  }

  "Real Induction" should "return 1D real induction" in {
    val ri = Provable.realInd(1)

    ri shouldBe 'proved
    ri.conclusion shouldBe ("==>" +
      "[{x__1'=f1(|t_|)&q(|t_|)}]p(|t_|)<->" +
      "(q(|t_|)->p(|t_|))&" +
      "[{x__1'=f1(|t_|)&q(|t_|)}t_:=0;]" +
      "((p(|t_|)&<{t_'=1,x__1'=f1(|t_|)&q(|t_|)|t_=0}>t_!=0-><{t_'=1,x__1'=f1(|t_|)&p(|t_|)|t_=0}>t_!=0)&" +
      "(!p(|t_|)&<{t_'=1,x__1'=-f1(|t_|)&q(|t_|)|t_=0}>t_!=0-><{t_'=1,x__1'=-f1(|t_|)&!p(|t_|)|t_=0}>t_!=0))").asSequent
  }

  it should "throw core exceptions on out-of-bounds dimension arguments" in {
    an[CoreException] should be thrownBy Provable.realInd(0)
    an[CoreException] should be thrownBy Provable.realInd(-1)
  }

  it should "return 2D real induction" in {
    val ri = Provable.realInd(2)

    ri shouldBe 'proved
    ri.conclusion shouldBe ("==>" +
      "[{x__1'=f1(|t_|),x__2'=f2(|t_|)&q(|t_|)}]p(|t_|)<->" +
      "(q(|t_|)->p(|t_|))&" +
      "[{x__1'=f1(|t_|),x__2'=f2(|t_|)&q(|t_|)}t_:=0;]" +
      "((p(|t_|)&<{t_'=1,x__1'=f1(|t_|),x__2'=f2(|t_|)&q(|t_|)|t_=0}>t_!=0-><{t_'=1,x__1'=f1(|t_|),x__2'=f2(|t_|)&p(|t_|)|t_=0}>t_!=0)&" +
      "(!p(|t_|)&<{t_'=1,x__1'=-f1(|t_|),x__2'=-f2(|t_|)&q(|t_|)|t_=0}>t_!=0-><{t_'=1,x__1'=-f1(|t_|),x__2'=-f2(|t_|)&!p(|t_|)|t_=0}>t_!=0))").asSequent
  }
}