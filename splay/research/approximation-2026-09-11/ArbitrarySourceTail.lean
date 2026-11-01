import Splay.Interface.RootDecayBridge

/-! The original literal source decay with an independently selected number
of halving blocks. Compression needs a cutoff based on the NEW logarithmic
range, not the original fixed insignificantThreshold. -/

namespace Splay.Research.ArbitrarySourceTail

open Splay.Interface
open scoped BigOperators

def threshold (params : Parameters) (blocks : ℕ) : ℕ :=
  params.exemptPasses + params.matchingDenominator * blocks

theorem profiles {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)} {occurrences : List (ActivityOccurrence n)}
    (history : ActivityHistory params initial initialLabels operations occurrences final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (blocks tailSteps : ℕ) :
    ∃ (prefixProfile : FiberProfile params (params.matchingDenominator*blocks))
      (tail : FiberProfile params tailSteps) (initialBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, params.exemptPasses) history initialBatches ∧
      prefixProfile.mass 0 = DescendantBatches.beforeMass initialBatches ∧
      (∀ index, tail.activity index = lineageRunActivity occurrences
        (root, threshold params blocks + index)) ∧
      2^blocks * tail.totalActivity ≤ prefixProfile.mass 0 := by
  classical
  have summaries : ∀ offset : ℕ, ∃ batches : List (DescendantBatch params),
      FiberBatchHistory params (root, params.exemptPasses+offset) history batches := by
    intro offset
    apply history.exists_nonexemptFiberBatches aligned
    omega
  let batches (offset : ℕ) : List (DescendantBatch params) := Classical.choose (summaries offset)
  have batchSummary (offset : ℕ) :
      FiberBatchHistory params (root, params.exemptPasses+offset) history (batches offset) :=
    Classical.choose_spec (summaries offset)
  let profile (base steps : ℕ) : FiberProfile params steps :=
    { mass := fun index => DescendantBatches.beforeMass (batches (base+index))
      activity := fun index => lineageRunActivity occurrences
        (root, params.exemptPasses+(base+index))
      layer := by
        intro index indexLt
        have current := batchSummary (base+index)
        have next : FiberBatchHistory params
            (root, (params.exemptPasses+(base+index))+1) history (batches (base+(index+1))) := by
          simpa only [Nat.add_assoc] using batchSummary (base+(index+1))
        have coverage : SuccessorFiberCoverage history root
            (params.exemptPasses+(base+index)) :=
          history.successorFiberCoverage_of_initial initialState aligned
          root (params.exemptPasses+(base+index)) (by omega)
        exact current.toSuccessorFiberLayer next coverage }
  let prefixProfile := profile 0 (params.matchingDenominator*blocks)
  let tail := profile (params.matchingDenominator*blocks) tailSteps
  have continuous : tail.mass 0 ≤ prefixProfile.mass (params.matchingDenominator*blocks) := by
    dsimp [tail, prefixProfile, profile]
    simp
  have scaled := prefixProfile.scaled_tailActivity_le_initialMass tail continuous
    (blocks := blocks) (scale := 2^blocks) rfl (le_refl _)
  refine ⟨prefixProfile, tail, batches 0, ?_, ?_, ?_, scaled⟩
  · simpa using batchSummary 0
  · dsimp [prefixProfile, profile]
  · intro index
    dsimp [tail, profile, threshold]
    congr 2
    omega

theorem root_tail_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {operations : List (Operation n)} {occurrences : List (ActivityOccurrence n)}
    {conversions : List ConversionOccurrence}
    (history : ActivityHistory params initial [] operations occurrences final finalLabels)
    (conversionHistory : RootConversionHistory params initial [] operations conversions final finalLabels)
    (initialState : initial.Initial params) (root : RootId) (blocks : ℕ) :
    2^blocks * rootTailActivity occurrences (threshold params blocks) root ≤
      rootConversionMass conversions root := by
  obtain ⟨prefixProfile, tail, initialBatches, summary, initialMass, activityEq, scaled⟩ :=
    profiles history initialState (by simp [initialState.2]) root blocks
      (operations.length-threshold params blocks)
  have converted := summary.beforeMass_le_rootConversionMass_of_initial
    conversionHistory initialState (by simp [initialState.2]) (by omega)
  have bounded := history.occurrence_passCount_lt_length_of_initial initialState
  have tailEq : tail.totalActivity = rootTailActivity occurrences (threshold params blocks) root := by
    unfold FiberProfile.totalActivity
    have functions : tail.activity = fun index =>
        lineageRunActivity occurrences (root, threshold params blocks+index) := funext activityEq
    rw [functions, sum_tailFibers_eq_rootTailCount occurrences (threshold params blocks)
      operations.length root bounded, rootTailActivity_eq_rootTailCount]
  rw [tailEq, initialMass] at scaled
  exact scaled.trans converted

theorem global_tail_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {operations : List (Operation n)} {occurrences : List (ActivityOccurrence n)}
    {conversions : List ConversionOccurrence}
    (history : ActivityHistory params initial [] operations occurrences final finalLabels)
    (conversionHistory : RootConversionHistory params initial [] operations conversions final finalLabels)
    (initialState : initial.Initial params) (blocks : ℕ) :
    2^blocks * tailActivity occurrences (threshold params blocks) ≤
      (conversions.map ConversionOccurrence.convertedMass).sum := by
  rw [tailActivity_eq_sum_rootTailActivity, Finset.mul_sum]
  exact (Finset.sum_le_sum (fun root _ =>
    root_tail_bound history conversionHistory initialState root blocks)).trans
    (RootConversionMass.sum_le_total conversions (tailRoots occurrences (threshold params blocks)))

theorem entry_tail_bound {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {operations : List (Operation n)} {occurrences : List (ActivityOccurrence n)}
    {conversions : List ConversionOccurrence}
    (history : ActivityHistory params initial [] operations occurrences final finalLabels)
    (conversionHistory : RootConversionHistory params initial [] operations conversions final finalLabels)
    (initialState : initial.Initial params) (blocks : ℕ) :
    2^blocks * tailActivity occurrences (threshold params blocks) ≤
      totalActivity operations + totalInserts operations := by
  have decay := global_tail_bound history conversionHistory initialState blocks
  have balance := conversionHistory.growingMass_balance
  have empty : initial.growingMass = 0 := by simp [State.growingMass, growingMassBlocks, initialState.2]
  rw [empty, zero_add] at balance
  omega

#print axioms entry_tail_bound

end Splay.Research.ArbitrarySourceTail
