package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

/**
  * Created by bbohrer on 12/28/15.
  */
@SummaryTest
@UsualTest
class AxiomInfoTests extends TacticTestBase with Matchers with BeforeAndAfterEach {
 "Axiom Info" should "exist for all axioms" in withZ3 { _ =>
   try {
     DerivationInfoRegistry.init
     DerivedAxioms.prepopulateDerivedLemmaDatabase
     ProvableSig.axiom.keys.forall({ case axiomName => AxiomInfo(axiomName); true }) shouldBe true
   } catch {
     case e:AxiomNotFoundException =>
       println("Test failed: Axiom not implemented: " + e.axiomName)
       throw e
   }
 }
}
