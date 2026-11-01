import Splay.Interface.ActivityTail
import Splay.Interface.PassCountBound
import Splay.Interface.RootPhaseHistory

namespace Splay.Interface

open scoped BigOperators

namespace RootConversionMass

@[simp]
theorem cons (occurrence : ConversionOccurrence)
    (occurrences : List ConversionOccurrence) (root : RootId) :
    rootConversionMass (occurrence :: occurrences) root =
      (if occurrence.root = root then occurrence.convertedMass else 0) +
        rootConversionMass occurrences root := by
  by_cases same : occurrence.root = root <;>
    simp [rootConversionMass, same]

/--
Root filtering never duplicates converted population: summing the filtered
mass over any finite set of distinct root IDs is bounded by the unfiltered
conversion total.
-/
theorem sum_le_total
    (occurrences : List ConversionOccurrence)
    (roots : Finset RootId) :
    ∑ root ∈ roots, rootConversionMass occurrences root ≤
      (occurrences.map ConversionOccurrence.convertedMass).sum := by
  classical
  induction occurrences with
  | nil =>
      simp [rootConversionMass]
  | cons occurrence occurrences ih =>
      simp_rw [RootConversionMass.cons]
      rw [Finset.sum_add_distrib]
      have indicator_le :
          (∑ root ∈ roots,
              if occurrence.root = root
              then occurrence.convertedMass else 0) ≤
            occurrence.convertedMass := by
        have indicator_eq :=
          Finset.sum_ite_eq' roots occurrence.root
            (fun _ => occurrence.convertedMass)
        rw [show
          (∑ root ∈ roots,
              if occurrence.root = root
              then occurrence.convertedMass else 0) =
            (if occurrence.root ∈ roots
              then occurrence.convertedMass else 0) by
            simpa only [eq_comm] using indicator_eq]
        split <;> omega
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add indicator_le ih

end RootConversionMass

namespace FiberBatchHistory

/--
The initial mass of a genuine decay prefix is paid by the exact conversion
reservoir carrying the same root label.
-/
theorem prefixMass_le_rootConversionMass_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {activityOccurrences : List (ActivityOccurrence n)}
    {conversionOccurrences : List ConversionOccurrence}
    {activityHistory :
      ActivityHistory params initial initialLabels operations
        activityOccurrences final finalLabels}
    {root : RootId}
    {prefixProfile :
      FiberProfile params (FiberProfile.decaySteps params)}
    {initialBatches : List (DescendantBatch params)}
    (initialSummary :
      FiberBatchHistory params (root, params.exemptPasses)
        activityHistory initialBatches)
    (initialMass :
      prefixProfile.mass 0 =
        DescendantBatches.beforeMass initialBatches)
    (conversionHistory :
      RootConversionHistory params initial initialLabels operations
        conversionOccurrences final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length) :
    prefixProfile.mass 0 ≤
      rootConversionMass conversionOccurrences root := by
  rw [initialMass]
  exact
    initialSummary.beforeMass_le_rootConversionMass_of_initial
      conversionHistory initialState aligned (by omega)

end FiberBatchHistory

/--
Pointwise root-reservoir bounds aggregate to the exact global conversion
mass, independently of which finite root set is selected.
-/
theorem sum_rootMass_le_conversionMass
    (occurrences : List ConversionOccurrence)
    (roots : Finset RootId) (mass : RootId → ℕ)
    (mass_le :
      ∀ root ∈ roots,
        mass root ≤ rootConversionMass occurrences root) :
    ∑ root ∈ roots, mass root ≤
      (occurrences.map ConversionOccurrence.convertedMass).sum := by
  calc
    ∑ root ∈ roots, mass root ≤
        ∑ root ∈ roots, rootConversionMass occurrences root :=
      Finset.sum_le_sum fun root root_mem => mass_le root root_mem
    _ ≤ (occurrences.map
          ConversionOccurrence.convertedMass).sum :=
      RootConversionMass.sum_le_total occurrences roots

/--
A decay charge selected for one root, retaining exactly the two facts needed
after the profile itself has been hidden: its chronological tail-fiber sum
and its bound by that root's conversion reservoir.
-/
structure RootDecaySelection
    (params : Parameters) (tailSteps : ℕ)
    {n : ℕ} (activityOccurrences : List (ActivityOccurrence n))
    (conversionOccurrences : List ConversionOccurrence)
    (root : RootId) where
  charge : RootDecayCharge (4 * params.valueBound)
  tailActivity_eq :
    charge.tailActivity =
      ((List.range tailSteps).map fun index =>
        lineageRunActivity activityOccurrences
          (root,
            FiberProfile.insignificantThreshold params + index)).sum
  converted_le :
    charge.convertedMass ≤
      rootConversionMass conversionOccurrences root

private theorem lineageRunActivity_cons
    {n : ℕ} (occurrence : ActivityOccurrence n)
    (occurrences : List (ActivityOccurrence n))
    (key : LineageRunKey) :
    lineageRunActivity (occurrence :: occurrences) key =
      (if occurrence.key = key then 1 else 0) +
        lineageRunActivity occurrences key := by
  by_cases same : occurrence.key = key <;>
    simp [lineageRunActivity, same, Nat.add_comm]

private theorem sum_indicator_of_nodup
    (items : List ℕ) (selected : ℕ) (nodup : items.Nodup) :
    (items.map fun item => if item = selected then 1 else 0).sum =
      if selected ∈ items then 1 else 0 := by
  induction items with
  | nil =>
      rfl
  | cons item items ih =>
      have tail_nodup := (List.nodup_cons.mp nodup).2
      rw [List.map_cons, List.sum_cons, ih tail_nodup]
      by_cases same : item = selected
      · subst item
        have not_tail := (List.nodup_cons.mp nodup).1
        simp [not_tail]
      · simp [same, Ne.symm same]

/--
Consecutive tail fibers count exactly the direct high-count occurrences of
one root once the chosen range covers every recorded pass count.
-/
theorem sum_tailFibers_eq_rootTailCount
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold steps : ℕ) (root : RootId)
    (bounded :
      ∀ occurrence ∈ occurrences,
        occurrence.passCount < steps) :
    ((List.range (steps - threshold)).map fun index =>
        lineageRunActivity occurrences
          (root, threshold + index)).sum =
      rootTailCount occurrences threshold root := by
  induction occurrences with
  | nil =>
      simp [lineageRunActivity, rootTailCount]
  | cons occurrence occurrences ih =>
      have occurrence_bound :
          occurrence.passCount < steps :=
        bounded occurrence (by simp)
      have tail_bound :
          ∀ later ∈ occurrences, later.passCount < steps := by
        intro later later_mem
        exact bounded later (by simp [later_mem])
      simp_rw [lineageRunActivity_cons]
      rw [List.sum_map_add, ih tail_bound]
      by_cases selected :
          occurrence.root = root ∧
            threshold ≤ occurrence.passCount
      · let index := occurrence.passCount - threshold
        have index_lt : index < steps - threshold := by
          dsimp [index]
          omega
        have indicator_eq :
            ((List.range (steps - threshold)).map fun candidate =>
                if occurrence.key = (root, threshold + candidate)
                then 1 else 0).sum = 1 := by
          calc
            ((List.range (steps - threshold)).map fun candidate =>
                  if occurrence.key = (root, threshold + candidate)
                  then 1 else 0).sum =
                ((List.range (steps - threshold)).map fun candidate =>
                  if candidate = index then 1 else 0).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro candidate candidate_mem
              by_cases same : candidate = index
              · subst candidate
                simp [ActivityOccurrence.key, index, selected.1]
                omega
              · have key_ne :
                    occurrence.key ≠
                      (root, threshold + candidate) := by
                  intro key_eq
                  apply same
                  dsimp [ActivityOccurrence.key] at key_eq
                  have count_eq :=
                    congrArg Prod.snd key_eq
                  dsimp [index]
                  omega
                simp [same, key_ne]
            _ = 1 := by
              rw [sum_indicator_of_nodup _ index
                List.nodup_range]
              simp [List.mem_range, index_lt]
        rw [indicator_eq]
        simp [rootTailCount, selected, Nat.add_comm]
      · have indicator_eq :
            ((List.range (steps - threshold)).map fun candidate =>
                if occurrence.key = (root, threshold + candidate)
                then 1 else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro value value_mem
          obtain ⟨candidate, candidate_mem, value_eq⟩ :=
            List.mem_map.mp value_mem
          subst value
          have key_ne :
              occurrence.key ≠
                (root, threshold + candidate) := by
            intro key_eq
            apply selected
            constructor
            · exact congrArg Prod.fst key_eq
            · have count_eq := congrArg Prod.snd key_eq
              change
                occurrence.passCount = threshold + candidate
                at count_eq
              omega
          simp [key_ne]
        rw [indicator_eq]
        simp [rootTailCount, selected]

namespace RootDecaySelection

/-- A selected profile tail is the exact high-count activity of its root. -/
theorem tailActivity_eq_rootTailActivity
    {n : ℕ} {params : Parameters} {tailSteps : ℕ}
    {activityOccurrences : List (ActivityOccurrence n)}
    {conversionOccurrences : List ConversionOccurrence}
    {root : RootId}
    (selection :
      RootDecaySelection params tailSteps activityOccurrences
        conversionOccurrences root)
    {steps : ℕ}
    (tailSteps_eq :
      tailSteps =
        steps - FiberProfile.insignificantThreshold params)
    (bounded :
      ∀ occurrence ∈ activityOccurrences,
        occurrence.passCount < steps) :
    selection.charge.tailActivity =
      rootTailActivity activityOccurrences
        (FiberProfile.insignificantThreshold params) root := by
  rw [selection.tailActivity_eq, tailSteps_eq,
    sum_tailFibers_eq_rootTailCount
      activityOccurrences
        (FiberProfile.insignificantThreshold params)
        steps root bounded,
    rootTailActivity_eq_rootTailCount]

end RootDecaySelection

namespace ActivityHistory

/-- Every root has a concrete decay selection charged to its exact reservoir. -/
theorem exists_rootDecaySelection_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {activityOccurrences : List (ActivityOccurrence n)}
    {conversionOccurrences : List ConversionOccurrence}
    (history :
      ActivityHistory params initial initialLabels operations
        activityOccurrences final finalLabels)
    (conversionHistory :
      RootConversionHistory params initial initialLabels operations
        conversionOccurrences final finalLabels)
    (initialState : initial.Initial params)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (tailSteps : ℕ) :
    Nonempty
      (RootDecaySelection params tailSteps activityOccurrences
        conversionOccurrences root) := by
  obtain
      ⟨prefixProfile, tail, initialBatches, initialSummary,
        initialMass, convertedBound, continuous, activityEq, scaled⟩ :=
    history.exists_decayProfiles_le_rootConversion_of_initial
      conversionHistory initialState aligned root tailSteps
  let charge : RootDecayCharge (4 * params.valueBound) :=
    { convertedMass := prefixProfile.mass 0
      tailActivity := tail.totalActivity
      scaled_tail_le := scaled }
  refine
    ⟨{ charge := charge
       tailActivity_eq := ?_
       converted_le := convertedBound }⟩
  dsimp [charge]
  unfold FiberProfile.totalActivity
  apply congrArg List.sum
  apply List.map_congr_left
  intro index index_mem
  exact activityEq index

end ActivityHistory

namespace ActivityHistory

/--
Summing the selected root profiles gives the exact global high-count activity,
paid by the chronological conversion mass with no duplicated reservoir.
-/
theorem global_tailActivity_le_conversionMass_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {finalLabels : RootLabels}
    {operations : List (Operation n)}
    {activityOccurrences : List (ActivityOccurrence n)}
    {conversionOccurrences : List ConversionOccurrence}
    (history :
      ActivityHistory params initial [] operations
        activityOccurrences final finalLabels)
    (conversionHistory :
      RootConversionHistory params initial [] operations
        conversionOccurrences final finalLabels)
    (initialState : initial.Initial params) :
    4 * params.valueBound *
        tailActivity activityOccurrences
          (FiberProfile.insignificantThreshold params) ≤
      (conversionOccurrences.map
        ConversionOccurrence.convertedMass).sum := by
  classical
  let threshold := FiberProfile.insignificantThreshold params
  let tailSteps := operations.length - threshold
  have bounded :
      ∀ occurrence ∈ activityOccurrences,
        occurrence.passCount < operations.length :=
    history.occurrence_passCount_lt_length_of_initial initialState
  let selection (root : RootId) :
      RootDecaySelection params tailSteps activityOccurrences
        conversionOccurrences root :=
    Classical.choice
      (history.exists_rootDecaySelection_of_initial
        conversionHistory initialState
          (by simp [initialState.2]) root tailSteps)
  have root_bound :
      ∀ root ∈ tailRoots activityOccurrences threshold,
        4 * params.valueBound *
            rootTailActivity activityOccurrences threshold root ≤
          rootConversionMass conversionOccurrences root := by
    intro root root_mem
    have tail_eq :
        (selection root).charge.tailActivity =
          rootTailActivity activityOccurrences threshold root := by
      apply
        (selection root).tailActivity_eq_rootTailActivity
          (steps := operations.length)
      · rfl
      · exact bounded
    calc
      4 * params.valueBound *
            rootTailActivity activityOccurrences threshold root =
          4 * params.valueBound *
            (selection root).charge.tailActivity := by
        rw [tail_eq]
      _ ≤ (selection root).charge.convertedMass :=
        (selection root).charge.scaled_tail_le
      _ ≤ rootConversionMass conversionOccurrences root :=
        (selection root).converted_le
  rw [tailActivity_eq_sum_rootTailActivity]
  rw [Finset.mul_sum]
  exact
    (Finset.sum_le_sum root_bound).trans
      (RootConversionMass.sum_le_total conversionOccurrences
        (tailRoots activityOccurrences threshold))

end ActivityHistory

namespace Trace

/--
Concrete global decay witness for a trace.  The returned activity list is the
same chronological annotation used to define the high-count tail.
-/
theorem exists_tailActivity_decay_bound
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ (finalLabels : RootLabels)
        (activityOccurrences : List (ActivityOccurrence n))
        (conversionOccurrences : List ConversionOccurrence),
      ActivityHistory params initial [] operations
          activityOccurrences final finalLabels ∧
        RootConversionHistory params initial [] operations
          conversionOccurrences final finalLabels ∧
        4 * params.valueBound *
            tailActivity activityOccurrences
              (FiberProfile.insignificantThreshold params) ≤
          totalActivity operations + totalInserts operations := by
  obtain ⟨finalLabels, lineageHistory, aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨activityOccurrences, activityHistory⟩ :=
    ActivityHistory.lift lineageHistory
  obtain ⟨conversionOccurrences, conversionHistory⟩ :=
    RootConversionHistory.lift lineageHistory
  have decay :=
    activityHistory.global_tailActivity_le_conversionMass_of_initial
      conversionHistory initialState
  have conversionBalance := conversionHistory.growingMass_balance
  have initialGrowingZero : initial.growingMass = 0 := by
    simp [State.growingMass, growingMassBlocks, initialState.2]
  rw [initialGrowingZero, zero_add] at conversionBalance
  refine
    ⟨finalLabels, activityOccurrences, conversionOccurrences,
      activityHistory, conversionHistory, decay.trans ?_⟩
  omega

/-- Existential form consumed by the final shift-charging assembly. -/
theorem exists_insignificantActivity_decay_bound
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ insignificantActivity : ℕ,
      4 * params.valueBound * insignificantActivity ≤
        totalActivity operations + totalInserts operations := by
  obtain
      ⟨finalLabels, activityOccurrences, conversionOccurrences,
        activityHistory, conversionHistory, decay⟩ :=
    trace.exists_tailActivity_decay_bound initialState
  exact
    ⟨tailActivity activityOccurrences
        (FiberProfile.insignificantThreshold params),
      decay⟩

end Trace

end Splay.Interface
