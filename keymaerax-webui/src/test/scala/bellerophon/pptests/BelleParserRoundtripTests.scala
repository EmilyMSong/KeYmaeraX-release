package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.btactics.{ArithmeticSimplification, FixedGenerator, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{AtomicODE, DifferentialSymbol, ODESystem, True}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest


/**
  * Tests BelleExpr roundtrip identity of parser and pretty printer.
  * @author Stefan Mitsch
  */
@UsualTest
class BelleParserRoundtripTests extends TacticTestBase {
  private val belleParser: String=>BelleExpr =
    if (false) BelleParser
    else new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _))

  private def roundTrip(tactic: String): Unit = BellePrettyPrinter(belleParser(tactic)) shouldBe tactic
  private def roundTrip(tactic: BelleExpr): Unit = belleParser(BellePrettyPrinter(tactic)) shouldBe tactic
  private def roundTrip(tactic: BelleExpr, ts: String): Unit = {
    belleParser(ts) shouldBe tactic
    BellePrettyPrinter(tactic) shouldBe ts
    // redundant
    roundTrip(tactic)
    roundTrip(ts)
  }

  //@note this test case points out something that's kind-of a problem with our current setup -- print(parse(x)) != x even if parse(print(x)) = x.
  //In order to get the actually correct behavior we would need DerivedAxiomInfo to be a bidirectional map and then we would need to always prefer that map's
  //names over the actual tactic that was created at the end of the day.
  "Parser and printer roundtrip" should "atomics" in withTactics {
    roundTrip(TactixLibrary.nil, "nil")
  }

  it should "position tactics with fixed positions" in withTactics {
    roundTrip(TactixLibrary.andR(1), "andR(1)")
  }

  it should "position tactics with locators" in withTactics {
    roundTrip(TactixLibrary.andL('L), "andL('L)")
    roundTrip(TactixLibrary.andR('R), "andR('R)")
  }

  it should "combinators" in withTactics {
    roundTrip(TactixLibrary.nil & TactixLibrary.nil, "nil ; nil")
    roundTrip(TactixLibrary.nil | TactixLibrary.nil, "nil | nil")
    roundTrip(OnAll(TactixLibrary.nil), "doall(nil)")
    roundTrip(TactixLibrary.nil*2, "nil*2")
    roundTrip(TactixLibrary.nil, "nil")
  }

  it should "input tactic transform" in withTactics {
    roundTrip(TactixLibrary.transform("x>0".asFormula)(1), """transform("x>0", 1)""")
  }

  it should "input tactic generalizeb" in withTactics {
    roundTrip(TactixLibrary.generalize("x>0".asFormula)(1), """MR("x>0", 1)""")
  }

  it should "input tactic diffCut" in withTactics {
    roundTrip(TactixLibrary.dC("x>0".asFormula)(1), """dC("x>0", 1)""")
  }

  it should "input tactic dG" in withTactics {
    roundTrip(TactixLibrary.dG("y'=0".asFormula, Some("1=1".asFormula))(1), """dG("y'=0", "1=1", 1)""")
    roundTrip(TactixLibrary.dG(ODESystem(AtomicODE(DifferentialSymbol("x".asVariable), "5*x+2".asTerm), True), None)(1), """dG("{x'=5*x+2&true}", 1)""")
    roundTrip(TactixLibrary.dG(ODESystem(AtomicODE(DifferentialSymbol("x".asVariable), "5*x+2".asTerm), True), Some("x>0".asFormula))(1), """dG("{x'=5*x+2&true}", "x>0", 1)""")
    // parsing from AtomicODE allowed to result in ODESystem, but will print as ODESystem (see roundtrip above)
    belleParser("""dG("{x'=5*x+2}", 1)""") shouldBe TactixLibrary.dG(ODESystem(AtomicODE(DifferentialSymbol("x".asVariable), "5*x+2".asTerm), True), None)(1)
  }

  it should "input tactic cut, cutL, cutR" in withTactics {
    roundTrip(TactixLibrary.cut("x>0".asFormula), """cut("x>0")""")
    roundTrip(TactixLibrary.cutL("x>0".asFormula)(AntePosition(1).checkTop), """cutL("x>0", -1)""")
    roundTrip(TactixLibrary.cutR("x>0".asFormula)(SuccPosition(1).checkTop), """cutR("x>0", 1)""")
    roundTrip(TactixLibrary.cutLR("x>0".asFormula)(SuccPosition(1).checkTop), """cutLR("x>0", 1)""")
  }

  it should "input tactic loop" in withTactics {
    roundTrip(TactixLibrary.loop("x>0".asFormula)(1), """loop("x>0", 1)""")
  }

  it should "input tactic boundRename" in withTactics {
    roundTrip(TactixLibrary.boundRename("x".asVariable, "y".asVariable)(1), """boundRename("x", "y", 1)""")
  }

  it should "input tactic stutter" in withTactics {
    //@todo test with BelleExpr data structure, but DLBySubst is private
    roundTrip("""stutter("y", 1)""")
  }

  it should "input tactic transform equality" in withTactics {
    roundTrip(ArithmeticSimplification.transformEquality("x=y".asFormula)(1), """transformEquality("x=y", 1)""")
  }

  it should "input tactic diffInvariant" in withTactics {
    roundTrip(TactixLibrary.diffInvariant("x^2=1".asFormula)(1), """diffInvariant("x^2=1", 1)""")
  }

  it should "two-position tactic cohide2" in withTactics {
    roundTrip(TactixLibrary.cohide2(-1, 1), "coHide2(-1, 1)")
  }

  it should "two-position tactic equivRewriting" ignore {
    //@todo test with BelleExpr data structure, but PropositionalTactics is private
    //@todo don't know how to print DependentTwoPositionTactics
    roundTrip("equivRewriting(-1, 1)")
  }

  it should "two-position tactic instantiatedEquivRewriting" in withTactics {
    //@todo test with BelleExpr data structure, but PropositionalTactics is private
    roundTrip("instantiatedEquivRewriting(-1, 1)")
  }

  it should "two-position tactic L2R" ignore {
    //@todo don't know how to print L2R
    roundTrip("L2R(-1, 1)")
  }


}
