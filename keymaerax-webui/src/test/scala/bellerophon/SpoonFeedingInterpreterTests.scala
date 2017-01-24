package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, SequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.{ExtractTacticFromTrace, InMemoryDB, ProofTree, TreeNode}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import testHelper.KeYmaeraXTestTags.SlowTest

import scala.collection.immutable._

/**
  * Tests the spoon-feeding interpreter.
  * Created by smitsch on 8/24/16.
  */
class SpoonFeedingInterpreterTests extends TacticTestBase {

  "Atomic tactic" should "be simply forwarded to the inner interpreter" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = false)
    tree.nodes should have size 2
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
  }

  "Sequential tactic" should "be split into atomics before being fed to inner" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    interpreter(implyR(1) & closeId, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 3
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 1
    tree.root.children.head.children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children.head.rule shouldBe "closeId"
  }

  "Either tactic" should "be explored and only successful outcome stored in database" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & (andR(1) | closeId), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 3
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 1
    tree.root.children.head.children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children.head.rule shouldBe "closeId"
  }

  "Branch tactic" should "work top-level" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & andR(1) & <(closeId, nil)")

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 7
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&x>=0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&x>=0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 2
    tree.root.children.head.children(0).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).rule shouldBe "andR(1)"
    tree.root.children.head.children(0).children should have size 1
    tree.root.children.head.children(0).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(0).children.head.rule shouldBe "closeId"
    tree.root.children.head.children(0).children.head.children shouldBe empty
    tree.root.children.head.children(1).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.children.head.children(1).rule shouldBe "andR(1)"
    tree.root.children.head.children(1).children should have size 1
    tree.root.children.head.children(1).children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.children.head.children(1).children.head.rule shouldBe "nil"
  }

  it should "work top-level and support complicated branch tactics" in withMathematica { tool => withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0&[{x'=1&x>=0}]x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, diffWeaken(1) & prop & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 7
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 2
    tree.root.children.head.children(0).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).rule shouldBe "andR(1)"
    tree.root.children.head.children(0).children should have size 1
    tree.root.children.head.children(0).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(0).children.head.rule shouldBe "closeId"
    tree.root.children.head.children(0).children.head.children shouldBe empty
    tree.root.children.head.children(1).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.children.head.children(1).rule shouldBe "andR(1)"
    tree.root.children.head.children(1).children should have size 1
    tree.root.children.head.children(1).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>=0->x>=0".asFormula))
    tree.root.children.head.children(1).children.head.rule shouldBe "diffWeaken(1)"
    tree.root.children.head.children(1).children.head.children should have size 1
    tree.root.children.head.children(1).children.head.children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(1).children.head.children.head.rule shouldBe "prop"
  }}

  it should "work with nested branching when every branch is closed" in withMathematica { tool => withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId & done, QE & done), QE & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 9
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0|x>1 -> x>0&x>=0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0|x>1".asFormula), IndexedSeq("x>0&x>=0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 2
    tree.root.children.head.children(0).sequent shouldBe Sequent(IndexedSeq("x>0|x>1".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).rule shouldBe "andR(1)"
    tree.root.children.head.children(0).children should have size 2
    tree.root.children.head.children(0).children(0).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).children(0).rule shouldBe "orL(-1)"
    tree.root.children.head.children(0).children(0).children should have size 1
    tree.root.children.head.children(0).children(0).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(0).children(0).children.head.rule shouldBe "closeId"
    tree.root.children.head.children(1).sequent shouldBe Sequent(IndexedSeq("x>0|x>1".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.children.head.children(1).rule shouldBe "andR(1)"
    tree.root.children.head.children(1).children should have size 1
    tree.root.children.head.children(1).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(1).children.head.rule shouldBe "QE"
  }}

  it should "work when early branches remain open and later ones close" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>1|x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & orL(-1) & Idioms.<(skip, closeId & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & orL(-1) & <(nil, closeId)")
  }

  it should "work with nested branching when branches stay open 1" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>1|x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(skip, closeId), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(nil, closeId), nil)")
  }

  it should "work with nested branching when branches stay open 2" in withDatabase { db =>
    val modelContent = "Variables. R x. End.\n\n Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId, skip), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(closeId, nil), nil)")
  }

  it should "should work with nested branching when branching stay open 3" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(implyR(1) & orL(-1) & Idioms.<(andR(1) & Idioms.<(closeId, skip), andR(1)),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & orL(-1) & <(andR(1) & <(closeId, nil), andR(1))")
  }

  "Parsed tactic" should "record STTT tutorial example 1 steps" taggedAs SlowTest in withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tacticText = """implyR('R) & andL('L) & diffCut({`v>=0`}, 1) & <(diffWeaken(1) & prop, diffInd(1))"""
    val tactic = BelleParser(tacticText)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(tacticText)
  }

  it should "record STTT tutorial example 2 steps" taggedAs SlowTest  in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(
      """
        |implyR(1) & andL('L) & andL('L) & loop({`v>=0`},1) & <(
        |  QE,
        |  QE,
        |  composeb(1) & choiceb(1) & andR(1) & <(
        |    assignb(1) & ODE(1),
        |    choiceb(1) & andR(1) & <(
        |      assignb(1) & ODE(1),
        |      assignb(1) & ODE(1)
        |    )
        |  )
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 3a steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 42 // no further testing necessary with this answer ;-)
  }}

  it should "record STTT tutorial example 4a steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 22
  }}

  it should "record STTT tutorial example 4b steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 11
  }}

  it should "record STTT tutorial example 9b steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 36
  }}

  it should "record STTT tutorial example 10 steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 50
  }}

  "Revealing internal steps" should "should work for diffInvariant" in withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR('R) & diffCut({`x>=old(x)`},1) & <(nil, diffInd(1))")
  }}

  it should "should work for multiple levels of diffInvariant without let" in withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 2)
    interpreter(implyR('R) & diffInvariant("x>=0".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |implyR('R) & (DCdiffcut({`x>=0`},1) & <(
        |  (nil&nil),
        |  (nil & (DI(1) & (implyR(1) & (andR(1) & <(
        |    close,
        |    (derive(1.1)&(DE(1)&(Dassignb(1.1)&(nil&(abstractionb(1)&QE))))) ))))) ))
      """.stripMargin)

    val reprove = proveBy(problem.asFormula, tactic)
    reprove.subgoals should have size 1
    reprove.subgoals.head.ante should contain only "x>=0".asFormula
    reprove.subgoals.head.succ should contain only "[{x'=1&true&x>=0}]x>=0".asFormula
  }}

  it should "should work for multiple levels of diffInvariant" ignore withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 2)
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |implyR('R) & (DCaxiom(1) & <(
        |  (nil&nil),
        |  (nil & (DI(1) & (implyR(1) & (andR(1) & <(
        |    close,
        |    partial(((derive(1.1)&DE(1))&(((((Dassignb(1.1))*1)&nil)&abstractionb(1))&(close|QE)))) ))))) ))
      """.stripMargin)

    //@todo reprove
  }}

  it should "should work for prop on a simple example" in withDatabase { db =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("nil & implyR(1) & closeId")

    val proofId2 = db.createProof(modelContent, "proof2")
    SpoonFeedingInterpreter(listener(db.db, proofId2), SequentialInterpreter, 1, strict=false)(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))
    db.extractTactic(proofId2) shouldBe BelleParser("implyR(1) & closeId")
  }

  it should "should work for prop on a left-branching example" in withDatabase { db =>
    val problem = "x>=0|!x<y -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("nil & implyR(1) & orL(-1) & <(closeId, notL(-1) & nil & nil)")

    val proofId2 = db.createProof(modelContent, "proof2")
    SpoonFeedingInterpreter(listener(db.db, proofId2), SequentialInterpreter, 1, strict=false)(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))
    db.extractTactic(proofId2) shouldBe BelleParser("implyR(1) & orL(-1) & <(closeId, notL(-1))")
  }

  it should "should work for prop with nested branching" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |nil & implyR(1) & orL(-1) & <(
        |  nil & andR(1) & <(
        |    closeId,
        |    nil
        |  )
        |  ,
        |  nil & andR(1) & <(
        |    nil,
        |    closeId
        |  )
        |)
      """.stripMargin)

    val proofId2 = db.createProof(modelContent, "proof2")
    SpoonFeedingInterpreter(listener(db.db, proofId2), SequentialInterpreter, 1, strict=false)(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    db.extractTactic(proofId2) shouldBe BelleParser(
      """
        |implyR(1) & orL(-1) & <(
        |  andR(1) & <(
        |    closeId,
        |    nil
        |  )
        |  ,
        |  andR(1) & <(
        |    nil,
        |    closeId
        |  )
        |)
      """.stripMargin)
  }

  private def stepInto(node: TreeNode, expectedStep: String, expectedDetails: BelleExpr, depth: Int = 1) = {
    val (localProvable, step) = node.endStep match {
      case Some(end) => (ProvableSig.startProof(end.input.subgoals(end.branch)), end.rule)
    }
    step shouldBe expectedStep
    val innerDb = new InMemoryDB()
    val localProofId = innerDb.createProof(localProvable)
    val innerInterpreter = SpoonFeedingInterpreter(listener(innerDb, localProofId, Some(localProvable)),
      SequentialInterpreter, depth, strict=false)
    innerInterpreter(BelleParser(step), BelleProvable(localProvable))
    val tactic = new ExtractTacticFromTrace(innerDb).apply(innerDb.getExecutionTrace(localProofId))
    tactic shouldBe expectedDetails
  }

  it should "work in the middle of a proof" in {
    val problem = "x>=0|x<y -> x>=0&x<y"
    val provable = ProvableSig.startProof(problem.asFormula)
    val db = new InMemoryDB()
    val proofId = db.createProof(provable)
    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & prop, BelleProvable(provable))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
    tree.findNode("2") match {
      case Some(node) =>
        val expected = BelleParser(
          """
            |orL(-1) & <(
            |  andR(1) & <(
            |    closeId,
            |    nil
            |  )
            |  ,
            |  andR(1) & <(
            |    nil,
            |    closeId
            |  )
            |)
          """.stripMargin)
        stepInto(node, "prop", expected)
    }
  }

  it should "work on a branch in the middle of a proof" in {
    val problem = "x>=0|x<y -> x>=0&x<y"
    val db = new InMemoryDB()

    val provable = ProvableSig.startProof(problem.asFormula)
    val proofId = db.createProof(provable)

    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & orL(-1) & onAll(prop), BelleProvable(provable))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId))
    tree.findNode("3") match {
      case Some(node) =>
        val expected = BelleParser(
          """
            |andR(1) & <(
            |  closeId,
            |  nil
            |)
          """.stripMargin)
        stepInto(node, "prop", expected)
    }

    tree.findNode("4") match {
      case Some(node) =>
        val expected = BelleParser(
          """
            |andR(1) & <(
            |  nil,
            |  closeId
            |)
          """.stripMargin)
        stepInto(node, "prop", expected)
    }
  }

  it should "should work on a typical example" in withDatabase { db => withMathematica { tool =>
    val problem = "x>=0 & y>=1 & z<=x+y & 3>2  -> [x:=x+y;]x>=z"
    val modelContent = s"Variables. R x. R y. R z. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(prop & unfoldProgramNormalize & QE, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("prop & unfold & QE")

    val tree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt))
    tree.findNode("1") match {
      case Some(node) =>
        val expected = BelleParser("implyR(1) & andL(-1) & andL(-2) & andL(-3)")
        stepInto(node, "prop", expected)
    }

    tree.findNode("2") match {
      case Some(node) =>
        val expected = BelleParser("chase('R) & normalize")
        stepInto(node, "unfold", expected)
    }

    tree.findNode("3") match {
      case Some(node) =>
        val expected = BelleParser("toSingleFormula & universalClosure(1) & rcf")
        stepInto(node, "QE", expected)
    }
  }}
}
