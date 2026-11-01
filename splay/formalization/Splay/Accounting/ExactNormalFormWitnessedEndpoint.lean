import Splay.Accounting.ScheduleExecutionProvenance

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Tree.BST
open OfflineOptimum

/--
The exact normal-form trace always has a concrete schedule-provenanced rich
execution at the natural height-scaled interface parameters.

Thus neither schedule construction, initialization, nor the value-bound
compatibility is part of the remaining exact translation boundary.  The only
shape-side premise is the canonical two-growing-block initialization limit.
-/
theorem exists_provenancedSchedule_of_normalForm
    {model : CostModel}
    (realization : Realization model)
    (shape : Interface.Shape)
    (growingLimit : 2 ≤ shape.growingLimit)
    {n : ℕ} (n_pos : 0 < n)
    (initialTree : BST 0 n)
    (accesses : List (Fin n)) :
    Nonempty
      (ProvenancedInitializedRealizedNormalFormSchedule
        (heightParameters shape
          (realization.comparisonProfile.maxHeight accesses))
        initialTree
        (realization.trace n n_pos accesses)) := by
  let comparison := realization.trace n n_pos accesses
  let height := realization.comparisonProfile.maxHeight accesses
  have traceHeight :
      comparison.initialTree.height ≤ height := by
    simpa [comparison, height, ComparisonTrace.initialTree] using
      realization.trace_height_le_profile n_pos accesses 0
  have initializationBound :
      Analysis.contractedGap
          (Rank.Snapshot.ofTree comparison.initialTree).maxRank ≤
        (heightParameters shape height).valueBound :=
    ofTree_contractedGap_le_heightParameters traceHeight shape
  have parameterGrowingLimit :
      2 ≤ (heightParameters shape height).growingLimit := by
    exact growingLimit
  exact
    ProvenancedInitializedRealizedNormalFormSchedule.exists_of_complete
      comparison initialTree parameterGrowingLimit initializationBound

/--
An exact trace-specific translation boundary.

Unlike `RealizedWitnessedThreeLawTranslationHypothesis`, this proposition
does not allow the accounting witness to choose an unrelated comparison
trace of merely comparable numerical cost.  It fixes the comparison trace
definitionally to the exact trace selected by the supplied normal-form
realization.  Consequently its schedule, rich event execution, height
parameter, and comparison-cost parameter all refer to the same selected
normal-form run.
-/
def ExactNormalFormRealizedWitnessedTranslationHypothesis
    {model : CostModel}
    (realization : Realization model)
    (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ (constants : TranslationConstants)
        (bendConstants : BendConstants),
      PotentialCoefficientDominance constants
          insertConstant valueChangeConstant ∧
        ∀ (n : ℕ), ∀ n_pos : 0 < n,
          ∀ (initialTree : BST 0 n)
            (accesses : List (Fin n)),
            Nonempty
              (RealizedWitnessedThreeLawCertificate
                constants bendConstants shape
                insertConstant valueChangeConstant
                n (realization.comparisonProfile.cost accesses)
                (realization.comparisonProfile.maxHeight accesses)
                initialTree accesses
                (realization.trace n n_pos accesses))

/--
Forgetting that the comparison trace is definitionally the normal-form
realization recovers the earlier schedule-bound translation hypothesis.
-/
theorem realizedWitnessedTranslationHypothesis_of_exactNormalForm
    {model : CostModel}
    {realization : Realization model}
    {shape : Interface.Shape}
    (exact :
      ExactNormalFormRealizedWitnessedTranslationHypothesis
        realization shape) :
    RealizedWitnessedThreeLawTranslationHypothesis
      realization.comparisonProfile shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, bendConstants, dominance, certificates⟩ :=
    exact insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, bendConstants, dominance, ?_⟩
  intro n nPositive initialTree accesses
  exact
    ⟨realization.trace n nPositive accesses,
      certificates n nPositive initialTree accesses⟩

/--
Concrete offline endpoint fixing the accounting comparison trace exactly.

The normal-form hypothesis selects the comparison trace.  The translation
witness is tied to that exact trace and to its concrete initialized rich
schedule, rather than choosing another trace with the same numerical profile.
-/
theorem
    targetBound_of_offlineNormalForm_and_exactRealizedWitnessedTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ExactNormalFormRealizedWitnessedTranslationHypothesis
        normalForm.realize shape) :
    TargetBound concreteOfflineCostModel :=
  targetBound_of_offlineNormalForm_and_realizedWitnessedTranslation
    normalForm shape
      (realizedWitnessedTranslationHypothesis_of_exactNormalForm
        translation)

/--
Exact-normal-form variant retaining the recursive provenance of the rich
transition through every concrete schedule constructor.
-/
def ExactNormalFormProvenancedWitnessedTranslationHypothesis
    {model : CostModel}
    (realization : Realization model)
    (shape : Interface.Shape) : Prop :=
  ∀ (insertConstant valueChangeConstant : ℕ),
    0 < insertConstant →
    0 < valueChangeConstant →
    ∃ (constants : TranslationConstants)
        (bendConstants : BendConstants),
      PotentialCoefficientDominance constants
          insertConstant valueChangeConstant ∧
        ∀ (n : ℕ), ∀ n_pos : 0 < n,
          ∀ (initialTree : BST 0 n)
            (accesses : List (Fin n)),
            Nonempty
              (ProvenancedRealizedWitnessedThreeLawCertificate
                constants bendConstants shape
                insertConstant valueChangeConstant
                n (realization.comparisonProfile.cost accesses)
                (realization.comparisonProfile.maxHeight accesses)
                initialTree accesses
                (realization.trace n n_pos accesses))

/--
Forgetting that the comparison trace is fixed recovers the uniform
schedule-provenanced translation premise.
-/
theorem
    provenancedRealizedWitnessedTranslationHypothesis_of_exactNormalForm
    {model : CostModel}
    {realization : Realization model}
    {shape : Interface.Shape}
    (exact :
      ExactNormalFormProvenancedWitnessedTranslationHypothesis
        realization shape) :
    ProvenancedRealizedWitnessedThreeLawTranslationHypothesis
      realization.comparisonProfile shape := by
  intro insertConstant valueChangeConstant
    insertPositive valueChangePositive
  obtain ⟨constants, bendConstants, dominance, certificates⟩ :=
    exact insertConstant valueChangeConstant
      insertPositive valueChangePositive
  refine ⟨constants, bendConstants, dominance, ?_⟩
  intro n nPositive initialTree accesses
  exact
    ⟨realization.trace n nPositive accesses,
      certificates n nPositive initialTree accesses⟩

/--
Strongest exact-trace endpoint without the structural neighbor-depth
strengthening: both the selected normal-form trace and the recursive
schedule-to-event provenance are fixed in the witness type.
-/
theorem
    targetBound_of_offlineNormalForm_and_exactProvenancedWitnessedTranslation
    (normalForm :
      Assumptions.NormalForm.Hypothesis concreteOfflineCostModel)
    (shape : Interface.Shape)
    (translation :
      ExactNormalFormProvenancedWitnessedTranslationHypothesis
        normalForm.realize shape) :
    TargetBound concreteOfflineCostModel :=
  targetBound_of_offlineNormalForm_and_provenancedRealizedTranslation
    normalForm shape
      (provenancedRealizedWitnessedTranslationHypothesis_of_exactNormalForm
        translation)

end Splay.Accounting
