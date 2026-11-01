import Splay.Accounting.WitnessedThreeLaw

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Tree.BST

/-- Semantic pairing and bend witnesses with the weighted potential budget
of the same rich trace. No bound on the unweighted number of productive
operations is required: a paid macro can perform several unit increases. -/
structure WeightedWitnessedThreeLawCertificate
    (constants : TranslationConstants) (bendConstants : BendConstants)
    (shape : Interface.Shape) (insertConstant valueChangeConstant : ℕ)
    (n nearCost height : ℕ) (initialTree : BST 0 n) (accesses : List (Fin n))
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
  important_le : pairingClassification.importantMoves.length ≤
    importantEnvelope constants n nearCost height
  unimportant_le : pairingClassification.unimportantMoves.length ≤
    unimportantEnvelope constants height
      (Interface.totalActivity (Lazy.eraseOperations events))
  potential_budget :
    PotentialBudget constants.semantic insertConstant valueChangeConstant
      params (Lazy.eraseOperations events) nearCost height
      (paidEnvelope constants n nearCost height
        (unimportantEnvelope constants height
          (Interface.totalActivity (Lazy.eraseOperations events))))
      (unimportantEnvelope constants height
        (Interface.totalActivity (Lazy.eraseOperations events)))
  bendWitness : ConcreteZigZagBendWitness bendConstants initialTree accesses comparison
  comparisonCost_le : comparison.cost ≤ nearCost
  bendCoefficient_le : bendConstants.coefficient ≤ constants.semantic.bends

namespace WeightedWitnessedThreeLawCertificate

/-- All event counts come from the supplied rich trace; pairing activity
retains its existing semantic classification. -/
noncomputable def toThreeLaw
    {constants : TranslationConstants} {bendConstants : BendConstants}
    {shape : Interface.Shape} {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ} {initialTree : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses}
    (witness : WeightedWitnessedThreeLawCertificate constants bendConstants shape
      insertConstant valueChangeConstant n nearCost height initialTree accesses comparison) :
    ThreeLawTranslationCertificate constants shape insertConstant valueChangeConstant
      n nearCost height initialTree accesses := by
  refine
    { params := witness.params
      initial := witness.richInitial.toInterface
      final := witness.richFinal.toInterface
      operations := Lazy.eraseOperations witness.events
      shape_eq := witness.shape_eq
      initialState := witness.pairingClassification.passClassification.initialState
      trace := witness.pairingClassification.passClassification.trace
      potential_budget := witness.potential_budget
      zigZig_pairings := ?_
      zigZag_bends := concrete_zigZag_bends witness.bendWitness
        witness.comparisonCost_le witness.bendCoefficient_le }
  have important : witness.pairingClassification.passClassification.importantSlots.length ≤
      importantEnvelope constants n nearCost height := by
    rw [← witness.pairingClassification.importantMoves_length]
    exact witness.important_le
  have unimportant : witness.pairingClassification.passClassification.unimportantSlots.length ≤
      unimportantEnvelope constants height
        (Interface.totalActivity (Lazy.eraseOperations witness.events)) := by
    rw [← witness.pairingClassification.unimportantMoves_length]
    exact witness.unimportant_le
  exact witness.pairingClassification.passClassification.zigZig_pairings.trans
    (Nat.add_le_add (Nat.add_le_add important unimportant) le_rfl)

end WeightedWitnessedThreeLawCertificate

/-- Compatibility with the previous, stronger productive-slot certificate.
The conversion preserves the exact events and the pairing/bend witnesses. -/
noncomputable def WitnessedThreeLawCertificate.toWeighted
    {constants : TranslationConstants} {bendConstants : BendConstants}
    {shape : Interface.Shape} {insertConstant valueChangeConstant : ℕ}
    {n nearCost height : ℕ} {initialTree : BST 0 n} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses} (n_pos : 0 < n)
    (dominance : PotentialCoefficientDominance constants insertConstant valueChangeConstant)
    (witness : WitnessedThreeLawCertificate constants bendConstants shape
      insertConstant valueChangeConstant n nearCost height initialTree accesses comparison) :
    WeightedWitnessedThreeLawCertificate constants bendConstants shape
      insertConstant valueChangeConstant n nearCost height initialTree accesses comparison where
  params := witness.params
  richInitial := witness.richInitial
  richFinal := witness.richFinal
  events := witness.events
  shape_eq := witness.shape_eq
  pairingClassification := witness.pairingClassification
  important_le := witness.important_le
  unimportant_le := witness.unimportant_le
  potential_budget :=
    witness.potentialResidue.toEnvelopePotentialResidue.toPotentialBudget n_pos dominance
  bendWitness := witness.bendWitness
  comparisonCost_le := witness.comparisonCost_le
  bendCoefficient_le := witness.bendCoefficient_le

end Splay.Accounting
