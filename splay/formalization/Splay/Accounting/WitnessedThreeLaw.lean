import Splay.Accounting.BoundaryPairingMove
import Splay.Accounting.ProductiveEventClassification
import Splay.Accounting.ZigZagBend
import Splay.Lazy.VisibleTraceOccurrence

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Tree.BST

/--
Semantic witnesses sufficient for the final three-law certificate.

This record replaces each bare numerical law by the strongest checked object
currently available:

* a concrete transcript partition whose internal charges name actual pass
  tuples;
* the one remaining productive-event charge after the verified potential
  reduction; and
* an exact numerical bend history tied to a concrete comparison trace.

The two boundary-list envelope estimates remain explicit because their proof
needs the manuscript's persistent lazy-interval and unbroken-block geometry.
-/
structure WitnessedThreeLawCertificate
    (constants : TranslationConstants)
    (bendConstants : BendConstants)
    (shape : Interface.Shape)
    (insertConstant valueChangeConstant : ℕ)
    (n nearCost height : ℕ)
    (initialTree : BST 0 n) (accesses : List (Fin n))
    (comparison : ComparisonTrace n accesses) where
  params : Interface.Parameters
  richInitial : Lazy.State n
  richFinal : Lazy.State n
  events : List (Lazy.Event n)
  shape_eq : params.toShape = shape

  pairingClassification :
    BoundaryPassPairingClassification
      (concreteSplayTranscript initialTree accesses).transcript
      params richInitial richFinal events

  important_le :
    pairingClassification.importantMoves.length ≤
      importantEnvelope constants n nearCost height
  unimportant_le :
    pairingClassification.unimportantMoves.length ≤
      unimportantEnvelope constants height
        (Interface.totalActivity (Lazy.eraseOperations events))

  potentialResidue :
    WitnessedEnvelopePotentialResidue constants params
      (Lazy.eraseOperations events) nearCost height

  bendWitness :
    ConcreteZigZagBendWitness bendConstants
      initialTree accesses comparison
  comparisonCost_le :
    comparison.cost ≤ nearCost
  bendCoefficient_le :
    bendConstants.coefficient ≤ constants.semantic.bends

namespace WitnessedThreeLawCertificate

/--
Every internally charged tuple occurs as an actual visible event of the rich
trace, even when arbitrarily many silent structural events are interleaved.
-/
theorem internalCharge_richPairingValid
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (witness :
      WitnessedThreeLawCertificate constants bendConstants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses comparison)
    (charge :
      PairingSlot ×
        Interface.ActivitySlot (Lazy.eraseOperations witness.events))
    (_member :
      charge ∈
        witness.pairingClassification.passClassification.internalCharges) :
    ∃ eventIndex before after sourceBlock,
      Lazy.Trace.VisibleStepAt witness.pairingClassification.trace
          charge.2.operationIndex.val eventIndex before
          (.pass charge.2.source charge.2.matching) after ∧
        before.toInterface.block? charge.2.source = some sourceBlock ∧
        Interface.PairingValid before.toInterface charge.2.source
          sourceBlock charge.2.pairing :=
  charge.2.exists_richPairingValid witness.pairingClassification.trace

/--
Every paid or unimportant productive slot is an actual insert/increase event
of this same rich trace.
-/
theorem productiveSlot_richStep
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (witness :
      WitnessedThreeLawCertificate constants bendConstants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses comparison)
    (index : ℕ)
    (member :
      index ∈
          witness.potentialResidue.productiveClassification.classification.paidSlots ∨
        index ∈
          witness.potentialResidue.productiveClassification.classification.unimportantSlots) :
    ∃ eventIndex before operation after,
      Lazy.Trace.VisibleStepAt witness.pairingClassification.trace
          index eventIndex before operation after ∧
        Interface.Operation.Productive operation := by
  let classification :=
    witness.potentialResidue.productiveClassification.classification
  have inClasses :
      index ∈
        classification.paidSlots ++ classification.unimportantSlots := by
    simpa only [List.mem_append, classification] using member
  have inCanonical :
      index ∈
        productiveOperationIndices
          (Lazy.eraseOperations witness.events) :=
    classification.partition.mem_iff.mp inClasses
  exact
    exists_richProductiveStep
      witness.pairingClassification.trace inCanonical

/--
All three numerical laws are consequences of their checked semantic
witnesses.
-/
noncomputable def toThreeLaw
    {constants : TranslationConstants}
    {bendConstants : BendConstants}
    {shape : Interface.Shape}
    {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ}
    {initialTree : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (n_pos : 0 < n)
    (dominance :
      PotentialCoefficientDominance constants
        insertConstant valueChangeConstant)
    (witness :
      WitnessedThreeLawCertificate constants bendConstants shape
        insertConstant valueChangeConstant n nearCost height
        initialTree accesses comparison) :
    ThreeLawTranslationCertificate constants shape
      insertConstant valueChangeConstant n nearCost height
      initialTree accesses := by
  refine
    { params := witness.params
      initial := witness.richInitial.toInterface
      final := witness.richFinal.toInterface
      operations := Lazy.eraseOperations witness.events
      shape_eq := witness.shape_eq
      initialState :=
        witness.pairingClassification.passClassification.initialState
      trace :=
        witness.pairingClassification.passClassification.trace
      potential_budget := ?_
      zigZig_pairings := ?_
      zigZag_bends := ?_ }
  · exact
      witness.potentialResidue.toEnvelopePotentialResidue.toPotentialBudget
        n_pos dominance
  · have classified :=
      witness.pairingClassification.passClassification.zigZig_pairings
    have importantPassLe :
        witness.pairingClassification.passClassification.importantSlots.length ≤
          importantEnvelope constants n nearCost height := by
      rw [← witness.pairingClassification.importantMoves_length]
      exact witness.important_le
    have unimportantPassLe :
        witness.pairingClassification.passClassification.unimportantSlots.length ≤
          unimportantEnvelope constants height
            (Interface.totalActivity
              (Lazy.eraseOperations witness.events)) := by
      rw [← witness.pairingClassification.unimportantMoves_length]
      exact witness.unimportant_le
    calc
      2 * (concreteSplayTranscript initialTree accesses).zigZig ≤
          witness.pairingClassification.passClassification.importantSlots.length +
            witness.pairingClassification.passClassification.unimportantSlots.length +
            Interface.totalActivity
              (Lazy.eraseOperations witness.events) :=
        classified
      _ ≤ importantEnvelope constants n nearCost height +
            unimportantEnvelope constants height
              (Interface.totalActivity
                (Lazy.eraseOperations witness.events)) +
            Interface.totalActivity
              (Lazy.eraseOperations witness.events) :=
        Nat.add_le_add
          (Nat.add_le_add importantPassLe unimportantPassLe)
          le_rfl
  · exact
      concrete_zigZag_bends
        witness.bendWitness
        witness.comparisonCost_le witness.bendCoefficient_le

end WitnessedThreeLawCertificate

/--
Uniform witnessed replacement for `ThreeLawTranslationHypothesis`.

The constants and coefficient dominance are uniform.  Each instance supplies
an actual comparison trace below the advertised profile cost and the semantic
witness record above.
-/
def WitnessedThreeLawTranslationHypothesis
    (comparisonProfile : ComparisonProfile)
    (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ (constants : TranslationConstants)
        (bendConstants : BendConstants),
      PotentialCoefficientDominance constants
          insertConstant valueChangeConstant ∧
        ∀ (n : ℕ), 0 < n →
          ∀ (initialTree : BST 0 n) (accesses : List (Fin n)),
            ∃ comparison : ComparisonTrace n accesses,
              Nonempty
                (WitnessedThreeLawCertificate
                  constants bendConstants shape
                  insertConstant valueChangeConstant
                  n (comparisonProfile.cost accesses)
                  (comparisonProfile.maxHeight accesses)
                  initialTree accesses comparison)

/--
Forgetting the semantic witnesses recovers the existing final three-law
translation hypothesis.
-/
theorem threeLawTranslationHypothesis_of_witnessed
    {comparisonProfile : ComparisonProfile}
    {shape : Interface.Shape}
    (witnessed :
      WitnessedThreeLawTranslationHypothesis comparisonProfile shape) :
    ThreeLawTranslationHypothesis comparisonProfile shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, bendConstants, dominance, witnesses⟩ :=
    witnessed insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, ?_⟩
  intro n nPositive initialTree accesses
  obtain ⟨comparison, ⟨witness⟩⟩ :=
    witnesses n nPositive initialTree accesses
  exact ⟨witness.toThreeLaw nPositive dominance⟩

/--
Direct accounting endpoint from the witnessed semantic residue.
-/
theorem hypothesis_of_witnessedThreeLawTranslation
    (optCost : {n : ℕ} → List (Fin n) → ℕ)
    {comparisonProfile : ComparisonProfile}
    (shape : Interface.Shape)
    (requests : RequestCostDominates comparisonProfile)
    (witnessed :
      WitnessedThreeLawTranslationHypothesis comparisonProfile shape) :
    Hypothesis (concreteSplayCostModel optCost) comparisonProfile :=
  hypothesis_of_threeLawTranslation optCost shape requests
    (threeLawTranslationHypothesis_of_witnessed witnessed)

end Splay.Accounting
