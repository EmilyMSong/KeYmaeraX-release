/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tags.{UsualTest, SummaryTest}
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import scala.collection.immutable._
import org.scalatest.{Matchers, FlatSpec}


/**
 * Created by aplatzer on 7/28/15.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class UnificationMatchTest extends FlatSpec with Matchers {
  Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
  Tactics.KeYmaeraScheduler.init(Map())

  private def should(e1: Expression, e2: Expression, us: Option[USubst]): Unit = {
    if (us.isDefined) {
      println("Expression: " + e1)
      println("Expression: " + e2)
      val s = UnificationMatch(e1, e2)
      println("Unified:  " + s)
      println("Expected: " + us.get)
      s shouldBe (/*us.get,*/ RenUSubst(us.get))
    } else {
      println("Expression: " + e1)
      println("Expression: " + e2)
      println("Expected: " + "<ununifiable>")
      a [UnificationException] should be thrownBy UnificationMatch(e1, e2)
    }
  }

  private def shouldUnify(e1: Expression, e2: Expression, us: USubst): Unit = should(e1,e2,Some(us))

  "Unification terms" should "unify f() with x^2+y" in {
    shouldUnify("f()".asTerm, "x^2+y".asTerm, USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil))
  }

  it should "unify f(x) with x^2+y" in {
    shouldUnify("f(x)".asTerm, "x^2+y".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f() with 3+(x^2+y)" in {
    shouldUnify("3+f()".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil))
  }

  it should "unify 3+f(x) with 3+(x^2+y)" in {
    shouldUnify("3+f(x)".asTerm, "3+(x^2+y)".asTerm, USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil))
  }


  "Unification formulas" should "unify p() with x^2+y>=0" in {
    shouldUnify("p()".asFormula, "x^2+y>=0".asFormula, USubst(
      SubstitutionPair("p()".asFormula, "x^2+y>=0".asFormula) :: Nil))
  }

  it should "unify \\forall x p(x) with \\forall x (!q(x)) " in {
    shouldUnify("\\forall x p(x)".asFormula, "\\forall x (!q(x))".asFormula, USubst(
      SubstitutionPair("p(.)".asFormula, "!q(.)".asFormula) :: Nil))
  }

  it should "match \\forall x p(x) with \\forall x (!p(x)) " in {
    shouldUnify("\\forall x p(x)".asFormula, "\\forall x (!p(x))".asFormula, USubst(
      SubstitutionPair("p(.)".asFormula, "!p(.)".asFormula) :: Nil))
  }

  "Unification programs" should "unify [a;]x>=0 with [x:=x+5;]x>=0" in {
    shouldUnify("[a;]x>=0".asFormula, "[x:=x+5;]x>=0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil))
  }

  it should "unify [a;x:=7;]x>=0 with [x:=x+5;x:=7;]x>=0" in {
    shouldUnify("[a;x:=7;]x>=0".asFormula, "[x:=x+5;x:=7;]x>=0".asFormula, USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil))
  }

  ignore/*"Old unification match"*/ should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (fails)" in {
    val s1 = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    import edu.cmu.cs.ls.keymaerax.tactics._
    //@todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe RenUSubst(new USubst(
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm)) ::
        SubstitutionPair(Variable("x"), Variable("y")) ::
        SubstitutionPair("t()".asTerm, Variable("z")) :: Nil))
  }

  // new unification matchers from now on
  import edu.cmu.cs.ls.keymaerax.bellerophon.{RenUSubst, UnificationMatch}

  "New unification match" should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0 (failed setup)" in {
    val s1 = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    import edu.cmu.cs.ls.keymaerax.btactics._
    //@todo not sure about the expected result
    a[CoreException] shouldBe thrownBy(
    UnificationMatch(s1, s2) shouldBe RenUSubst(new USubst(
      SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm)) ::
        SubstitutionPair(Variable("x"), Variable("y")) ::
        SubstitutionPair("t()".asTerm, Variable("z")) :: Nil))
    )
  }

  it should "unify (\\forall x p(x)) -> p(t()) with (\\forall y y>0) -> z>0" in {
    val s1 = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall x p(x) -> p(t())".asFormula))
    val s2 = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall y y>0 -> z>0".asFormula))
    println("Unify " + s1 + "\nwith  " + s2 + "\nyields " + UnificationMatch(s1, s2))
    //@todo not sure about the expected result
    UnificationMatch(s1, s2) shouldBe RenUSubst(
      (PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm)) ::
        (Variable("x"), Variable("y")) ::
        ("t()".asTerm, Variable("z")) :: Nil)
  }

  it should "unify [x:=f();]p(x) with [x:=7+x;]x^2>=5" in {
    UnificationMatch("[x:=f();]p(x)".asFormula, "[x:=7+x;]x^2>=5".asFormula) shouldBe RenUSubst(
        ("f()".asTerm, "7+x".asTerm) ::
          (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil)
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [x:=7+x;]x^2>=5 <-> (7+x)^2>=5" in {
    UnificationMatch("[x:=f();]p(x) <-> p(f())".asFormula, "[x:=7+x;]x^2>=5 <-> (7+x)^2>=5".asFormula) shouldBe RenUSubst(
      ("f()".asTerm, "7+x".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil)
  }

  it should "unify [x:=f();]p(x) with [y:=7+z;]y^2>=5" in {
    UnificationMatch("[x:=f();]p(x)".asFormula, "[y:=7+z;]y^2>=5".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y")) ::
      ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil)
  }

  it should "unify [x:=f();]p(x) <-> p(f()) with [y:=7+z;]y^2>=5 <-> (7+z)^2>=5" in {
    UnificationMatch("[x:=f();]p(x) <-> p(f())".asFormula, "[y:=7+z;]y^2>=5 <-> (7+z)^2>=5".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y")) ::
        ("f()".asTerm, "7+z".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil)
  }

  it should "unify y>0 -> [x:=2;]y>0 with p() -> [a;]p()" in {
    UnificationMatch("p() -> [a;]p()".asFormula, "y>0 -> [x:=2;]y>0".asFormula) shouldBe RenUSubst(
      (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asFormula) ::
        (ProgramConst("a"), Assign(Variable("x"), Number(2))) :: Nil
    )
  }

  it should "unify [x:=2;]y>0 -> y>0 with [a;]p() -> p()" in {
    // not an axiom, just to test both directions
    UnificationMatch("[a;]p() -> p()".asFormula, "[x:=2;]y>0 -> y>0".asFormula) shouldBe RenUSubst(
      (ProgramConst("a"), Assign(Variable("x"), Number(2))) ::
        (PredOf(Function("p", None, Unit, Bool), Nothing), "y>0".asFormula) :: Nil
    )
  }

  it should "unify renaming and instance [y:=y;]p(??) and [y_0:=y_0;](y_0>77&true)" in {
    UnificationMatch("[y:=y;]p(??)".asFormula,
      "[y_0:=y_0;](y_0>77&true)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(y_0>77&true)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming and instance [y:=y;]p(??)<->p(??) and [y_0:=y_0;](true)<->(true)" in {
    UnificationMatch("[y:=y;]p(??)<->p(??)".asFormula,
      "[y_0:=y_0;](true)<->(true)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(true)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming x=0 and y_0=0" in {
    UnificationMatch("x=0".asFormula,
      "y_0=0".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming x=0<->x=0 and y_0=0<->y_0=0" in {
    UnificationMatch("x=0<->x=0".asFormula,
      "y_0=0<->y_0=0".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming x=0&x=0<->x=0 and y_0=0&y_0=0<->y_0=0" in {
    UnificationMatch("x=0&x=0<->x=0".asFormula,
      "y_0=0&y_0=0<->y_0=0".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming x=0<->x=0&x=0 and y_0=0<->y_0=0&y_0=0" in {
    UnificationMatch("x=0<->x=0&x=0".asFormula,
      "y_0=0<->y_0=0&y_0=0".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming x>1&x=2<->x<3 and y_0>1&y_0=2<->y_0<3" in {
    UnificationMatch("x>1&x=2<->x<3".asFormula,
      "y_0>1&y_0=2<->y_0<3".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming x>1<->x=2&x<3 and y_0>1<->y_0=2&y_0<3" in {
    UnificationMatch("x>1<->x=2&x<3".asFormula,
      "y_0>1<->y_0=2&y_0<3".asFormula) shouldBe RenUSubst(
      (Variable("x"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming and instance [y:=y;]y>5<->y>5 and [y_0:=y_0;]y_0>5<->y_0>5" in {
    UnificationMatch("[y:=y;]y>5<->y>5".asFormula,
      "[y_0:=y_0;]y_0>5<->y_0>5".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) :: Nil
    )
  }

  it should "unify renaming and instance p(??)<->[y:=y;]p(??) and (y_0=0)<->[y_0:=y_0;](y_0=0)" in {
    UnificationMatch("p(??)<->[y:=y;]p(??)".asFormula,
      "(y_0=0)<->[y_0:=y_0;](y_0=0)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(y_0=0)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming and instance [y:=y;]p(??)<->p(??) and [y_0:=y_0;](y_0=0)<->(y_0=0)" in {
    UnificationMatch("[y:=y;]p(??)<->p(??)".asFormula,
      "[y_0:=y_0;](y_0=0)<->(y_0=0)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(y_0=0)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming and instance p(??)<->[y:=y;]p(??) and (true)<->[y_0:=y_0;](true)" in {
    UnificationMatch("p(??)<->[y:=y;]p(??)".asFormula,
      "(true)<->[y_0:=y_0;](true)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(true)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming and instance p(??)<->[y:=y;]p(??) and (y_0>77&true)<->[y_0:=y_0;](y_0>77&true)" in {
    UnificationMatch("p(??)<->[y:=y;]p(??)".asFormula,
      "(y_0>77&true)<->[y_0:=y_0;](y_0>77&true)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(y_0>77&true)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming and instance [y:=y;]p(??)<->p(??) and [y_0:=y_0;](y_0>77&true)<->(y_0>77&true)" in {
    UnificationMatch("[y:=y;]p(??)<->p(??)".asFormula,
      "[y_0:=y_0;](y_0>77&true)<->(y_0>77&true)".asFormula) shouldBe RenUSubst(
      (Variable("y"), Variable("y",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(y_0>77&true)".asFormula) ::
        Nil
    )
  }

  it should "unify renaming and long instance" in {
    UnificationMatch("[x_:=x_;]p(??)<->p(??)".asFormula,
      "[x_0:=x_0;](((x_0>0&true)&true)&true->(2>=0|false)|false)<->((x_0>0&true)&true)&true->(2>=0|false)|false".asFormula) shouldBe RenUSubst(
      (Variable("x_"), Variable("x",Some(0))) ::
        (PredOf(Function("p", None, Real, Bool), Anything), "(((x_0>0&true)&true)&true->(2>=0|false)|false)".asFormula) ::
        Nil
    )
  }

  //@todo this test case would need the expensive reunify to be activated in UnificationMatch again
  ignore/*"Reunifier ideally"*/ should "unify p(f()) <-> [x:=f();]p(x) with (7+x)^2>=5 <-> [x:=7+x;]x^2>=5" in {
    UnificationMatch("p(f()) <-> [x:=f();]p(x)".asFormula, "(7+x)^2>=5 <-> [x:=7+x;]x^2>=5".asFormula) shouldBe RenUSubst(
      ("f()".asTerm, "7+x".asTerm) ::
        (PredOf(Function("p", None, Real, Bool), DotTerm), GreaterEqual(Power(DotTerm, "2".asTerm), "5".asTerm)) :: Nil)
  }
}
