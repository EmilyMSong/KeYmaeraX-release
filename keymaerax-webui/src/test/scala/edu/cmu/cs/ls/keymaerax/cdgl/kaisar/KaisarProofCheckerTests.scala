package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt

class KaisarProofCheckerTests extends TacticTestBase {
  import KaisarProof._
  val pc = ParserCommon
  val ep = ExpressionParser
  val pp = ProofParser
  val kp = KaisarKeywordParser

  //  class KPPTestException(msg: String) extends Exception (msg)

  def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] => x.value
      case x: Failure => throw new Exception(x.trace().toString)
    }

  "Proof checker" should "check assignments" in {
    val pfStr = "x:=1; ++ x:=2; ++ x:=3;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=1; ++ x:=2; ++ x:=3;]true".asFormula
  }

  it should "check compositions" in {
    val pfStr = "x := *; y := x^2;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; y:=x^2;]true".asFormula
  }


  it should "compose assertions" in withMathematica { _ =>
    val pfStr = "x := *; y := x^2; !p:(y >= 0) by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; y:=x^2; {?y>=0;}^@]true".asFormula
  }

  it should "compose assumption" in {
    val pfStr = "x := *; ?p:(x^2 = y & x >= 0);"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=*; ?(x^2 = y & x >= 0);]true".asFormula
  }


  it should "reject invalid auto step" in withMathematica { _ =>
    val pfStr  = "!falsehood:(1 <= 0) by auto;"
    val pf = p(pfStr, pp.assert(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "succeed switch" in withMathematica { _ =>
    val pfStr = "switch { case xNeg:(x <= 1) => !x: (true) by auto; case xPos:(x >= 0) => !x: (true) by auto;}"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{{?(x<=1); {?(true);}^@}^@ ++ {?(x>=0); {?(true);}^@}^@}^@]true".asFormula
  }

  it should "fail bad switch" in withMathematica { _ =>
    val pfStr = "switch { case xOne:(x >= 1) => !x: (true) by auto; case xNeg:(x < 0) => !x: (true) by auto;}"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "support paramaterized switch" in withMathematica { _ =>
    val pfStr = "?eitherOr: (x >= 1 | x < 0 | x = 1); switch (eitherOr) { case xOne:(x >= 1) => !x: (true) by auto; case xNeg:(x < 0) => !x:(true) by auto; case x =1 => !x: (true) by auto;}"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[?(x>=1|x<0|x=1);{{?(x>=1); {?(true);}^@}^@ ++ {?(x<0); {?(true);}^@}^@ ++{?(x=1); {?(true);}^@}^@}^@]true".asFormula
  }

  it should "reject mismatched case" in withMathematica { _ =>
    val pfStr = "?eitherOr: (x >= 1 | x < 0); switch (eitherOr) { case xOne:(x >= 1) => !x:(true) by auto; case xNeg:(x < 0) => !x: (true) by auto; case x=1 => !x: (true) by auto;}"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "support note" in withMathematica { _ =>
    val pfStr = "?l:(x = 1); ?r:(y = 0); note lr = andI(l, r);"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[?x=1;?y=0;{?(x=1&y=0);}^@]true".asFormula
  }

  it should "check admissibility for programs which aren't SSA" in withMathematica { _ =>
    val pfStr = "x:=x+1;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "ban ghost program variable escaping scope" in withMathematica { _ =>
    val pfStr = "x:=1; (G y:= 2; G) !p:(x + y = 3) by auto;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "ban inverse ghost proof variable escaping scope" in withMathematica { _ =>
    val pfStr = "{G ?p:(x = 0); G} !q:(x = 0) using p by auto;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe (thrownBy(ProofChecker(Context.empty, pf)))
  }

  it should "allow ghost proof variable escaping scope" in withMathematica { _ =>
    val pfStr = "?xVal:(x:=1); (G ?yVal:(y:= 2); !p:(x + y = 3) using andI(xVal, yVal) by auto; !q:(x > 0) using andI(p, yVal) by auto; G) !p:(x + 1 > 0) using q by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=1;{?(x+1>0);}^@]true".asFormula
  }

  it should "allow inverse ghost program variable escaping scope for tautological purposes" in withMathematica { _ =>
    val pfStr = "{G x := 0; G} !q:(x^2 >= 0) by auto;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[x:=0; {?(x^2 >= 0);}^@]true".asFormula
  }

  "ode proof checking" should "prove trivial  system proof" in withMathematica { _ =>
    val pfStr = "x' = y, y' = x;"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{x'=y,y'=x&true}]true".asFormula
  }

  it should "ban diffghost with no body" in withMathematica { _ =>
    val pfStr = "(G x' = y G);"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe thrownBy(ProofChecker(Context.empty, pf))
  }
  it should "prove diffghost" in withMathematica { _ =>
    val pfStr = "y' = y^2, (G x' = y G);"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{y'=y^2&true}]true".asFormula
  }

  it should "prove inverse diffghost" in withMathematica { _ =>
    val pfStr = "{G x' = y G};"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{x'=y&true}]true".asFormula
  }

  it should "prove diffweak" in withMathematica { _ =>
    val pfStr = "x' = y & {G dc:(x > 0) G};"
    val pf = p(pfStr, pp.statement(_))
    val (ss, ff) = ProofChecker(Context.empty, pf)
    ff shouldBe "[{x'=y&x>0}]true".asFormula
  }

  // @TODO: Still debugging ode proof checker, write more tests
  // @TODO: specifically, write tests with other programs after the ode, which look up ODE facts/assignments in context
  // And tests which use duration-assignments.
  it should "catch invalid dc-assign: not bound" in withMathematica { _ =>
    val pfStr = "x' = y & t := T;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe thrownBy(ProofChecker(Context.empty, pf))
  }

  it should "catch invalid dc-assign 2: not initialized" in withMathematica { _ =>
    val pfStr = "t' = 1, x' = y & t := T;"
    val pf = p(pfStr, pp.statement(_))
    a[ProofCheckException] shouldBe thrownBy(ProofChecker(Context.empty, pf))
  }


  // @TODO syntax: Should we use ? in domain constraint assumption syntax?
  // @TODO syntax: what should ghost vs inverse ghost syntax be?
  it should "prove solution cut that requires domain constraint assumption" in withMathematica { _ =>
    val pfStr = "t:= 0; ?xInit:(x:= 1);  {t' = 1, x' = -1 & xRange:(x >=0) & !tRange:(t <= 1) using xInit xRange by solution};"
    val pf = p(pfStr, pp.statement(_))
    a[ODEAdmissibilityException] shouldBe thrownBy(ProofChecker(Context.empty, pf))
  }

}
