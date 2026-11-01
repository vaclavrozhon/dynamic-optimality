import Splay.Interface.GlobalDecay

namespace Splay.Interface

/-- Fiber activity distributes exactly over concatenation of histories. -/
theorem lineageRunActivity_append {n : ℕ}
    (first second : List (ActivityOccurrence n))
    (key : LineageRunKey) :
    lineageRunActivity (first ++ second) key =
      lineageRunActivity first key +
        lineageRunActivity second key := by
  unfold lineageRunActivity
  rw [List.filter_append, List.length_append]

/--
One nonexempt descendant batch together with the exact legal history step
which realizes it.
-/
structure HeadFiberBatch {n : ℕ} {params : Parameters}
    (before : State n) (labels : RootLabels)
    (operation : Operation n) (after : State n)
    (key : LineageRunKey) (batch : DescendantBatch params) where
  sourceId : BlockId
  matching : List (Pairing n)
  source : Block n
  sourceRoot : RootId
  operation_eq : operation = .pass sourceId matching
  step : Step params before operation after
  aligned : labels.length = before.blocks.length
  source_found : before.block? sourceId = some source
  root_found : RootLabels.root? labels sourceId = some sourceRoot
  key_eq : (sourceRoot, source.passCount) = key
  nonexempt : params.exemptPasses ≤ source.passCount
  matching_valid :
    MatchingValid params before sourceId source matching
  batch_eq :
    batch =
      DescendantBatch.ofMatching matching_valid nonexempt

namespace HeadFiberBatch

/-- Every occurrence in the selected head pass has the selected fiber key. -/
theorem occurrence_key_eq
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {key : LineageRunKey}
    {batch : DescendantBatch params}
    (realized :
      HeadFiberBatch before labels operation after key batch) :
    ∀ occurrence ∈
        operationActivityOccurrences before labels operation,
      occurrence.key = key := by
  obtain
    ⟨realizedSourceId, realizedMatching, realizedSource,
      realizedRoot, operation_eq, realizedStep, realizedAligned,
      realizedSourceFound, realizedRootFound, realizedKeyEq,
      realizedNonexempt, realizedMatchingValid, realizedBatchEq⟩ :=
    realized
  subst operation
  intro occurrence member
  obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
    List.mem_map.mp member
  subst occurrence
  simp [ActivityOccurrence.key, realizedSourceFound,
    realizedRootFound, realizedKeyEq]

/-- The batch activity is exactly the selected head operation's fiber count. -/
theorem activity_eq
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {key : LineageRunKey}
    {batch : DescendantBatch params}
    (realized :
      HeadFiberBatch before labels operation after key batch) :
    batch.activity =
      lineageRunActivity
        (operationActivityOccurrences before labels operation) key := by
  have allKeys := realized.occurrence_key_eq
  obtain
    ⟨realizedSourceId, realizedMatching, realizedSource,
      realizedRoot, operation_eq, realizedStep, realizedAligned,
      realizedSourceFound, realizedRootFound, realizedKeyEq,
      realizedNonexempt, realizedMatchingValid, batch_eq⟩ :=
    realized
  subst operation
  subst batch
  have filter_all :
      (operationActivityOccurrences before labels
          (.pass realizedSourceId realizedMatching) |>.filter
        fun occurrence => decide (occurrence.key = key)) =
      operationActivityOccurrences before labels
        (.pass realizedSourceId realizedMatching) := by
    rw [List.filter_eq_self]
    intro occurrence member
    simpa using allKeys occurrence member
  unfold lineageRunActivity
  rw [filter_all]
  change realizedMatching.length =
    (operationActivityOccurrences before labels
      (.pass realizedSourceId realizedMatching)).length
  rw [length_operationActivityOccurrences]
  rfl

end HeadFiberBatch

/--
An exact chronological extraction of all actual batches carrying one fiber
key.  Skipped operations are certified to contribute zero activity to that
key; selected operations retain their complete `HeadFiberBatch` witness.
-/
inductive FiberBatchHistory {n : ℕ} (params : Parameters)
    (key : LineageRunKey) :
    ∀ {initial final : State n}
      {initialLabels finalLabels : RootLabels}
      {operations : List (Operation n)}
      {occurrences : List (ActivityOccurrence n)},
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels →
      List (DescendantBatch params) → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      FiberBatchHistory params key
        (ActivityHistory.nil (labels := labels) valid) []
  | skip {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailOccurrences : List (ActivityOccurrence n)}
      {batches : List (DescendantBatch params)}
      (head : Step params before operation middle)
      (tail :
        ActivityHistory params middle
          (RootLabels.after beforeLabels operation)
          operations tailOccurrences after afterLabels)
      (tailBatches :
        FiberBatchHistory params key tail batches)
      (head_zero :
        lineageRunActivity
          (operationActivityOccurrences before beforeLabels operation)
          key = 0) :
      FiberBatchHistory params key
        (ActivityHistory.cons head tail) batches
  | take {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailOccurrences : List (ActivityOccurrence n)}
      {batch : DescendantBatch params}
      {batches : List (DescendantBatch params)}
      (head : Step params before operation middle)
      (tail :
        ActivityHistory params middle
          (RootLabels.after beforeLabels operation)
          operations tailOccurrences after afterLabels)
      (headBatch :
        HeadFiberBatch before beforeLabels operation middle key batch)
      (tailBatches :
        FiberBatchHistory params key tail batches) :
      FiberBatchHistory params key
        (ActivityHistory.cons head tail) (batch :: batches)

namespace FiberBatchHistory

/-- Extracted batch activity is exactly the original occurrence fiber count. -/
theorem activity_eq
    {n : ℕ} {params : Parameters} {key : LineageRunKey}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    {history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels}
    {batches : List (DescendantBatch params)}
    (summary : FiberBatchHistory params key history batches) :
    DescendantBatches.activity batches =
      lineageRunActivity occurrences key := by
  induction summary with
  | nil =>
      rfl
  | @skip before middle after beforeLabels afterLabels operation operations
      tailOccurrences batches head tail tailBatches head_zero ih =>
      rw [lineageRunActivity_append, head_zero, zero_add]
      exact ih
  | @take before middle after beforeLabels afterLabels operation operations
      tailOccurrences batch batches head tail headBatch tailBatches ih =>
      simp only [DescendantBatches.activity, List.map_cons, List.sum_cons]
      rw [lineageRunActivity_append, headBatch.activity_eq]
      exact congrArg
        (lineageRunActivity
          (operationActivityOccurrences before beforeLabels operation)
          key + ·)
        ih

end FiberBatchHistory

/--
The sole global continuity obligation between two consecutive pass-count
fibers of one root lineage.

It says that every element appearing in a genuine source at count `i + 1`
survived some genuine source pass at count `i`.  Local `PassRun` decay,
split inheritance, and occurrence counting do not by themselves prove this
cross-time fact.
-/
def SuccessorFiberCoverage
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (root : RootId) (passCount : ℕ) : Prop :=
  ∀ {currentBatches nextBatches : List (DescendantBatch params)},
    FiberBatchHistory params (root, passCount)
        history currentBatches →
      FiberBatchHistory params (root, passCount + 1)
        history nextBatches →
      DescendantBatches.beforeMass nextBatches ≤
        DescendantBatches.afterMass currentBatches

namespace FiberBatchHistory

/--
Two automatically extracted consecutive summaries, plus the one explicit
successor-coverage fact, assemble the exact `FiberLayer` consumed by
`GlobalDecay`.
-/
def toSuccessorFiberLayer
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    {history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels}
    {root : RootId} {passCount : ℕ}
    {currentBatches nextBatches : List (DescendantBatch params)}
    (current :
      FiberBatchHistory params (root, passCount)
        history currentBatches)
    (next :
      FiberBatchHistory params (root, passCount + 1)
        history nextBatches)
    (coverage : SuccessorFiberCoverage history root passCount) :
    FiberLayer params
      (DescendantBatches.beforeMass currentBatches)
      (DescendantBatches.beforeMass nextBatches)
      (lineageRunActivity occurrences (root, passCount)) :=
  { batches := currentBatches
    current_eq := rfl
    next_le := coverage current next
    activity_eq := current.activity_eq.symm }

end FiberBatchHistory

private theorem headFiberBatch_or_zero
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (key : LineageRunKey)
    (nonexemptKey : params.exemptPasses ≤ key.2) :
    (∃ batch : DescendantBatch params,
      Nonempty
        (HeadFiberBatch before labels operation after key batch)) ∨
      lineageRunActivity
        (operationActivityOccurrences before labels operation) key = 0 := by
  cases operation with
  | convert blockId =>
      exact Or.inr (by
        simp [operationActivityOccurrences, lineageRunActivity])
  | create creator =>
      exact Or.inr (by
        simp [operationActivityOccurrences, lineageRunActivity])
  | insert blockId element =>
      exact Or.inr (by
        simp [operationActivityOccurrences, lineageRunActivity])
  | delete blockId element =>
      exact Or.inr (by
        simp [operationActivityOccurrences, lineageRunActivity])
  | @pass sourceId matching =>
      obtain ⟨source, source_found, _after_found⟩ :=
        step.2.1.pass_source?
      obtain ⟨source_lt, _⟩ :=
        List.getElem?_eq_some_iff.mp source_found
      have root_lt : sourceId < labels.length := by
        simpa [aligned] using source_lt
      let sourceRoot : RootId := labels[sourceId]
      have root_found :
          RootLabels.root? labels sourceId = some sourceRoot :=
        List.getElem?_eq_getElem root_lt
      let actualKey : LineageRunKey :=
        (sourceRoot, source.passCount)
      by_cases selected : actualKey = key
      · have source_nonexempt :
            params.exemptPasses ≤ source.passCount := by
          have count_eq :
              source.passCount = key.2 :=
            congrArg Prod.snd selected
          omega
        have matching_valid :
            MatchingValid params before sourceId source matching := by
          cases effect_eq : step.2.1 with
          | pass found valid_matching blocks_eq values_eq =>
              rename_i actualSource
              have actual_eq : actualSource = source := by
                rw [source_found] at found
                exact (Option.some.inj found).symm
              subst actualSource
              exact valid_matching
        let batch :=
          DescendantBatch.ofMatching matching_valid source_nonexempt
        exact Or.inl
          ⟨batch, ⟨
            { sourceId := sourceId
              matching := matching
              source := source
              sourceRoot := sourceRoot
              operation_eq := rfl
              step := step
              aligned := aligned
              source_found := source_found
              root_found := root_found
              key_eq := selected
              nonexempt := source_nonexempt
              matching_valid := matching_valid
              batch_eq := rfl }⟩⟩
      · apply Or.inr
        unfold lineageRunActivity
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro occurrence member
        simp only [decide_eq_true_eq]
        intro occurrence_key
        obtain ⟨actualSourceId, actualMatching, actualSource, pairing,
            actualRoot, operation_eq, actual_source_found,
            actual_root_found, pairing_mem, occurrence_eq⟩ :=
          mem_operationActivityOccurrences_of_step
            step aligned member
        have sourceId_eq : actualSourceId = sourceId := by
          exact (Operation.pass.inj operation_eq).1.symm
        subst actualSourceId
        have source_eq : actualSource = source := by
          rw [source_found] at actual_source_found
          exact (Option.some.inj actual_source_found).symm
        subst actualSource
        have root_eq : actualRoot = sourceRoot := by
          rw [root_found] at actual_root_found
          exact (Option.some.inj actual_root_found).symm
        subst actualRoot
        subst occurrence
        exact selected occurrence_key
  | split blockId prefixLength =>
      exact Or.inr (by
        simp [operationActivityOccurrences, lineageRunActivity])
  | valueChange element delta =>
      exact Or.inr (by
        simp [operationActivityOccurrences, lineageRunActivity])

namespace ActivityHistory

/--
Every aligned legal activity history automatically supplies the complete list
of genuine nonexempt descendant batches for a fixed `(root, passCount)` key.
-/
theorem exists_nonexemptFiberBatches
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    (key : LineageRunKey)
    (nonexemptKey : params.exemptPasses ≤ key.2) :
    ∃ batches : List (DescendantBatch params),
      FiberBatchHistory params key history batches := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid⟩
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length := by
        rw [RootLabels.length_after, aligned]
        exact head.2.1.blocks_length.symm
      obtain ⟨tailBatches, tailSummary⟩ :=
        ih nextAligned
      rcases headFiberBatch_or_zero head aligned key nonexemptKey with
          ⟨batch, ⟨headBatch⟩⟩ | headZero
      · exact
          ⟨batch :: tailBatches,
            .take head tail headBatch tailSummary⟩
      · exact
          ⟨tailBatches,
            .skip head tail tailSummary headZero⟩

/--
Concrete global decay bridge: no caller supplies local decay premises.
All actual activity in a nonexempt fiber is represented by legal matching
batches, hence automatically satisfies aggregate balance and weighted decay.
-/
theorem exists_nonexemptFiberDecay
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    (key : LineageRunKey)
    (nonexemptKey : params.exemptPasses ≤ key.2) :
    ∃ batches : List (DescendantBatch params),
      DescendantBatches.activity batches =
          lineageRunActivity occurrences key ∧
        DescendantBatches.afterMass batches +
            lineageRunActivity occurrences key ≤
          DescendantBatches.beforeMass batches ∧
        params.matchingDenominator *
              DescendantBatches.afterMass batches +
            params.matchingNumerator *
              DescendantBatches.beforeMass batches ≤
          params.matchingDenominator *
            DescendantBatches.beforeMass batches := by
  obtain ⟨batches, summary⟩ :=
    history.exists_nonexemptFiberBatches
      aligned key nonexemptKey
  have activity_eq := summary.activity_eq
  exact
    ⟨batches, activity_eq,
      by
        rw [← activity_eq]
        exact DescendantBatches.after_add_activity_le_before batches,
      DescendantBatches.weighted_decay batches⟩

/--
Automatic adjacent-fiber layer construction.  All balance and decay facts are
discharged from the legal history; only `SuccessorFiberCoverage` remains.
-/
theorem exists_nonexemptSuccessorFiberLayer
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    (root : RootId) (passCount : ℕ)
    (nonexempt : params.exemptPasses ≤ passCount)
    (coverage : SuccessorFiberCoverage history root passCount) :
    ∃ (currentBatches nextBatches : List (DescendantBatch params)),
      FiberBatchHistory params (root, passCount)
          history currentBatches ∧
        FiberBatchHistory params (root, passCount + 1)
          history nextBatches ∧
        Nonempty
          (FiberLayer params
            (DescendantBatches.beforeMass currentBatches)
            (DescendantBatches.beforeMass nextBatches)
            (lineageRunActivity occurrences (root, passCount))) := by
  obtain ⟨currentBatches, currentSummary⟩ :=
    history.exists_nonexemptFiberBatches
      aligned (root, passCount) nonexempt
  have next_nonexempt :
      params.exemptPasses ≤
        ((root, passCount + 1) : LineageRunKey).2 := by
    omega
  obtain ⟨nextBatches, nextSummary⟩ :=
    history.exists_nonexemptFiberBatches
      aligned (root, passCount + 1) next_nonexempt
  exact
    ⟨currentBatches, nextBatches, currentSummary, nextSummary,
      ⟨currentSummary.toSuccessorFiberLayer nextSummary coverage⟩⟩

end ActivityHistory

namespace Trace

/--
Trace-level form of the automatic nonexempt fiber decay extraction.
-/
theorem exists_nonexemptFiberDecay
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final)
    (key : LineageRunKey)
    (nonexemptKey : params.exemptPasses ≤ key.2) :
    ∃ (finalLabels : RootLabels)
        (occurrences : List (ActivityOccurrence n))
        (batches : List (DescendantBatch params)),
      ActivityHistory params initial [] operations occurrences
          final finalLabels ∧
        DescendantBatches.activity batches =
          lineageRunActivity occurrences key ∧
        DescendantBatches.afterMass batches +
            lineageRunActivity occurrences key ≤
          DescendantBatches.beforeMass batches ∧
        params.matchingDenominator *
              DescendantBatches.afterMass batches +
            params.matchingNumerator *
              DescendantBatches.beforeMass batches ≤
          params.matchingDenominator *
            DescendantBatches.beforeMass batches := by
  obtain ⟨finalLabels, lineageHistory, aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨occurrences, activityHistory⟩ :=
    ActivityHistory.lift lineageHistory
  obtain ⟨batches, activity_eq, balance, decay⟩ :=
    activityHistory.exists_nonexemptFiberDecay
      (by simp [initialState.2]) key nonexemptKey
  exact
    ⟨finalLabels, occurrences, batches, activityHistory,
      activity_eq, balance, decay⟩

end Trace

end Splay.Interface
