import Splay.Interface.Decay
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Splay.Interface

open scoped BigOperators

/--
One unit of pass activity, annotated by the ghost lineage of its source and
the source's inherited pre-pass count.

There is one occurrence per pairing, represented by its loser.  The
`(root, passCount)` key is exactly the level at which the global decay proof
has to aggregate activity across all split descendants of one root block.
-/
structure ActivityOccurrence (n : ℕ) where
  root : RootId
  source : BlockId
  passCount : ℕ
  loser : Element n
  deriving DecidableEq, Repr

/-- The lineage/pass-count key used to group activity occurrences. -/
abbrev LineageRunKey :=
  RootId × ℕ

namespace ActivityOccurrence

def key {n : ℕ} (occurrence : ActivityOccurrence n) : LineageRunKey :=
  (occurrence.root, occurrence.passCount)

end ActivityOccurrence

/--
The occurrences contributed by one operation at its actual pre-state.

The `getD` fallbacks make this a total transparent function.  For a legal
canonically labelled trace, the lookup-success theorem below proves that
neither fallback is used.
-/
def operationActivityOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels) :
    Operation n → List (ActivityOccurrence n)
  | .pass source matching =>
      let root := (RootLabels.root? labels source).getD source
      let passCount :=
        (before.block? source).map Block.passCount |>.getD 0
      matching.map fun pairing =>
        { root := root
          source := source
          passCount := passCount
          loser := pairing.loser }
  | _ => []

/-- The occurrence encoding preserves exactly one unit per pairing. -/
@[simp]
theorem length_operationActivityOccurrences {n : ℕ}
    (before : State n) (labels : RootLabels)
    (operation : Operation n) :
    (operationActivityOccurrences before labels operation).length =
      operation.activity := by
  cases operation <;> simp [operationActivityOccurrences,
    Operation.activity]

/--
On an aligned legal step, every encoded occurrence uses successful source and
lineage lookups and records the source's actual inherited pass count.
-/
theorem mem_operationActivityOccurrences_of_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {occurrence : ActivityOccurrence n}
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (member :
      occurrence ∈
        operationActivityOccurrences before labels operation) :
    ∃ (source : BlockId) (matching : List (Pairing n))
        (sourceBlock : Block n) (pairing : Pairing n)
        (sourceRoot : RootId),
      operation = .pass source matching ∧
        before.block? source = some sourceBlock ∧
        RootLabels.root? labels source = some sourceRoot ∧
        pairing ∈ matching ∧
        occurrence =
          { root := sourceRoot
            source := source
            passCount := sourceBlock.passCount
            loser := pairing.loser } := by
  cases operation with
  | convert block =>
      simp [operationActivityOccurrences] at member
  | create creator =>
      simp [operationActivityOccurrences] at member
  | insert block element =>
      simp [operationActivityOccurrences] at member
  | delete block element =>
      simp [operationActivityOccurrences] at member
  | @pass source matching =>
      obtain ⟨sourceBlock, sourceFound, _afterFound⟩ :=
        step.2.1.pass_source?
      obtain ⟨source_lt, _source_eq⟩ :=
        List.getElem?_eq_some_iff.mp sourceFound
      have label_lt : source < labels.length := by
        simpa [aligned] using source_lt
      let sourceRoot : RootId := labels[source]
      have rootFound :
          RootLabels.root? labels source = some sourceRoot :=
        List.getElem?_eq_getElem label_lt
      obtain ⟨pairing, pairingMember, occurrenceEq⟩ :=
        List.mem_map.mp member
      refine
        ⟨source, matching, sourceBlock, pairing, sourceRoot,
          rfl, sourceFound, rootFound, pairingMember, ?_⟩
      subst occurrence
      simp [sourceFound, rootFound]
  | split block prefixLength =>
      simp [operationActivityOccurrences] at member
  | valueChange element delta =>
      simp [operationActivityOccurrences] at member

/-- Existing lineage labels persist through every deterministic ghost update. -/
theorem RootLabels.mem_after {n : ℕ} {labels : RootLabels}
    {root : RootId} (member : root ∈ labels)
    (operation : Operation n) :
    root ∈ RootLabels.after labels operation := by
  cases operation <;> simp [RootLabels.after, member]

/-- A fixed-source pass run contributes exactly its `passRunActivity`. -/
theorem totalActivity_pass_operations {n : ℕ} (source : BlockId)
    (matchings : List (List (Pairing n))) :
    totalActivity
        (matchings.map fun matching => Operation.pass source matching) =
      passRunActivity matchings := by
  induction matchings with
  | nil =>
      rfl
  | cons matching matchings ih =>
      simp only [totalActivity, passRunActivity, List.map_cons,
        List.sum_cons, Operation.activity]
      exact congrArg (matching.length + ·) ih

/--
All activity in one contiguous fixed-source run is paid by elements removed
from its initial source.
-/
theorem PassRun.activity_le_initialSource
    {n : ℕ} {params : Parameters} {sourceId : BlockId}
    {initial final : State n}
    {matchings : List (List (Pairing n))}
    (run : PassRun params sourceId initial matchings final)
    {source : Block n}
    (sourceFound : initial.block? sourceId = some source) :
    passRunActivity matchings ≤ source.elements.length := by
  obtain ⟨finalSource, _finalFound, _creator, _count, _mode, balance⟩ :=
    run.source_evolution sourceFound
  omega

/--
A complete trace together with its deterministic activity annotations.

This is deliberately a relation indexed by the occurrence list.  It retains
the intermediate states needed to compute the source pass count while erasing
to the already verified `HistoryTrace`.
-/
inductive ActivityHistory {n : ℕ} (params : Parameters) :
    State n → RootLabels → List (Operation n) →
      List (ActivityOccurrence n) → State n → RootLabels → Prop
  | nil {state : State n} {labels : RootLabels}
      (valid : state.Valid params) :
      ActivityHistory params state labels [] [] state labels
  | cons {before middle after : State n}
      {beforeLabels afterLabels : RootLabels}
      {operation : Operation n} {operations : List (Operation n)}
      {tailOccurrences : List (ActivityOccurrence n)}
      (head : Step params before operation middle)
      (tail :
        ActivityHistory params middle
          (RootLabels.after beforeLabels operation)
          operations tailOccurrences after afterLabels) :
      ActivityHistory params before beforeLabels
        (operation :: operations)
        (operationActivityOccurrences before beforeLabels operation ++
          tailOccurrences)
        after afterLabels

namespace ActivityHistory

/-- Forgetting activity occurrences recovers the ghost-lineage history. -/
theorem erase {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels) :
    HistoryTrace params initial initialLabels operations final finalLabels := by
  induction history with
  | nil valid =>
      exact .nil valid
  | cons head tail ih =>
      exact .cons head ih

/-- Every lineage history admits its deterministic activity annotation. -/
theorem lift {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels) :
    ∃ occurrences,
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels := by
  induction history with
  | nil valid =>
      exact ⟨[], .nil valid⟩
  | @cons before middle after beforeLabels afterLabels operation operations
      head tail ih =>
      obtain ⟨tailOccurrences, annotatedTail⟩ := ih
      exact
        ⟨operationActivityOccurrences before beforeLabels operation ++
            tailOccurrences,
          .cons head annotatedTail⟩

/--
The annotation is an exact global accounting identity, not merely an upper
bound: its list length is total interface activity.
-/
theorem occurrences_length {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels) :
    occurrences.length = totalActivity operations := by
  induction history with
  | nil valid =>
      rfl
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      simp only [List.length_append,
        length_operationActivityOccurrences, totalActivity,
        List.map_cons, List.sum_cons]
      exact congrArg (operation.activity + ·) ih

/-- Alignment of lineage labels is inherited from `HistoryTrace`. -/
theorem labels_length {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length) :
    finalLabels.length = final.blocks.length :=
  history.erase.labels_length aligned

/-- The deterministic lineage update only appends labels. -/
theorem labels_monotone {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels) :
    ∀ {root}, root ∈ initialLabels → root ∈ finalLabels := by
  induction history with
  | nil valid =>
      intro root member
      exact member
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      intro root member
      exact ih (RootLabels.mem_after member operation)

/--
For an aligned legal history, every occurrence's source root is an actual
lineage label in the final ghost state.  Thus the total `getD` definition of
`operationActivityOccurrences` never invents an untracked root on traces
lifted from an initial state.
-/
theorem occurrence_root_mem_finalLabels
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length) :
    ∀ occurrence ∈ occurrences, occurrence.root ∈ finalLabels := by
  induction history with
  | nil valid =>
      simp
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length := by
        rw [RootLabels.length_after, aligned]
        exact head.2.1.blocks_length.symm
      have tailRoots := ih nextAligned
      intro occurrence occurrence_mem
      simp only [List.mem_append] at occurrence_mem
      rcases occurrence_mem with headOccurrence | tailOccurrence
      · cases operation with
        | convert block =>
            simp [operationActivityOccurrences] at headOccurrence
        | create creator =>
            simp [operationActivityOccurrences] at headOccurrence
        | insert block element =>
            simp [operationActivityOccurrences] at headOccurrence
        | delete block element =>
            simp [operationActivityOccurrences] at headOccurrence
        | @pass source matching =>
            obtain ⟨sourceBlock, sourceFound, _afterFound⟩ :=
              head.2.1.pass_source?
            obtain ⟨source_lt, _source_eq⟩ :=
              List.getElem?_eq_some_iff.mp sourceFound
            have label_lt : source < beforeLabels.length := by
              simpa [aligned] using source_lt
            let sourceRoot : RootId := beforeLabels[source]
            have rootFound :
                RootLabels.root? beforeLabels source =
                  some sourceRoot := by
              exact List.getElem?_eq_getElem label_lt
            obtain ⟨pairing, pairing_mem, occurrence_eq⟩ :=
              List.mem_map.mp headOccurrence
            subst occurrence
            have root_mem_before : sourceRoot ∈ beforeLabels :=
              List.getElem_mem label_lt
            have root_mem_next :
                sourceRoot ∈
                  RootLabels.after beforeLabels (.pass source matching) :=
              RootLabels.mem_after root_mem_before _
            have root_mem_final :
                sourceRoot ∈ afterLabels :=
              tail.labels_monotone root_mem_next
            simpa [operationActivityOccurrences, rootFound,
              sourceFound] using root_mem_final
        | split block prefixLength =>
            simp [operationActivityOccurrences] at headOccurrence
        | valueChange element delta =>
            simp [operationActivityOccurrences] at headOccurrence
      · exact tailRoots occurrence tailOccurrence

end ActivityHistory

/-- All lineage/pass-count keys that actually carry activity. -/
def lineageRunKeys {n : ℕ}
    (occurrences : List (ActivityOccurrence n)) : Finset LineageRunKey :=
  (occurrences.map ActivityOccurrence.key).toFinset

/-- Activity in one exact lineage/pass-count group. -/
def lineageRunActivity {n : ℕ}
    (occurrences : List (ActivityOccurrence n))
    (key : LineageRunKey) : ℕ :=
  (occurrences.filter fun occurrence =>
    decide (occurrence.key = key)).length

/--
Finite fiber-counting identity: grouping an occurrence list by its
lineage/pass-count key neither loses nor duplicates activity.
-/
theorem sum_lineageRunActivity {n : ℕ}
    (occurrences : List (ActivityOccurrence n)) :
    ∑ key ∈ lineageRunKeys occurrences,
        lineageRunActivity occurrences key =
      occurrences.length := by
  induction occurrences with
  | nil =>
      simp [lineageRunKeys, lineageRunActivity]
  | cons head tail ih =>
      have activity_cons (key : LineageRunKey) :
          lineageRunActivity (head :: tail) key =
            (if head.key = key then 1 else 0) +
              lineageRunActivity tail key := by
        by_cases same : head.key = key
        · simp [lineageRunActivity, same, Nat.add_comm]
        · simp [lineageRunActivity, same]
      have indicator_sum (keys : Finset LineageRunKey)
          (key_mem : head.key ∈ keys) :
          (∑ key ∈ keys,
            if head.key = key then 1 else 0) = 1 := by
        calc
          (∑ key ∈ keys,
              if head.key = key then 1 else 0) =
              (if head.key = head.key then 1 else 0) := by
                apply Finset.sum_eq_single_of_mem head.key key_mem
                intro other _ other_ne
                simp [Ne.symm other_ne]
          _ = 1 := by simp
      by_cases key_present :
          head.key ∈ lineageRunKeys tail
      · rw [show lineageRunKeys (head :: tail) =
            lineageRunKeys tail by
          unfold lineageRunKeys
          simp only [List.map_cons, List.toFinset_cons]
          exact Finset.insert_eq_of_mem key_present]
        calc
          ∑ key ∈ lineageRunKeys tail,
                lineageRunActivity (head :: tail) key =
              ∑ key ∈ lineageRunKeys tail,
                ((if head.key = key then 1 else 0) +
                  lineageRunActivity tail key) := by
                apply Finset.sum_congr rfl
                intro key _
                exact activity_cons key
          _ =
              (∑ key ∈ lineageRunKeys tail,
                  if head.key = key then 1 else 0) +
                ∑ key ∈ lineageRunKeys tail,
                  lineageRunActivity tail key := by
                exact Finset.sum_add_distrib
          _ = 1 + tail.length := by
                rw [ih]
                rw [indicator_sum _ key_present]
          _ = (head :: tail).length := by
                simp only [List.length_cons]
                omega
      · rw [show lineageRunKeys (head :: tail) =
            insert head.key (lineageRunKeys tail) by
          unfold lineageRunKeys
          simp only [List.map_cons, List.toFinset_cons]]
        have head_activity_zero :
            lineageRunActivity tail head.key = 0 := by
          unfold lineageRunActivity
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro occurrence occurrence_mem
          simp only [decide_eq_true_eq]
          intro occurrence_key
          apply key_present
          unfold lineageRunKeys
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨occurrence, occurrence_mem, occurrence_key⟩
        have tail_sum :
            (∑ key ∈ insert head.key (lineageRunKeys tail),
                lineageRunActivity tail key) = tail.length := by
          rw [Finset.sum_insert key_present, head_activity_zero,
            zero_add, ih]
        have inserted_indicator_sum :
            (∑ key ∈ insert head.key (lineageRunKeys tail),
                if head.key = key then 1 else 0) = 1 :=
          indicator_sum _ (Finset.mem_insert_self _ _)
        calc
          ∑ key ∈ insert head.key (lineageRunKeys tail),
                lineageRunActivity (head :: tail) key =
              ∑ key ∈ insert head.key (lineageRunKeys tail),
                ((if head.key = key then 1 else 0) +
                  lineageRunActivity tail key) := by
                apply Finset.sum_congr rfl
                intro key _
                exact activity_cons key
          _ =
              (∑ key ∈ insert head.key (lineageRunKeys tail),
                  if head.key = key then 1 else 0) +
                ∑ key ∈ insert head.key (lineageRunKeys tail),
                  lineageRunActivity tail key := by
                exact Finset.sum_add_distrib
          _ = 1 + tail.length := by
                rw [inserted_indicator_sum, tail_sum]
          _ = (head :: tail).length := by
                simp only [List.length_cons]
                omega

/--
Exact global grouping of interface activity by lineage and inherited pass
count.

This is the bridge missing between `History` and the fixed-source decay
lemmas: the remaining ActivityBound proof must bound these fibers across
split descendants, rather than treating only contiguous `PassRun`s.
-/
theorem ActivityHistory.totalActivity_eq_sum_lineageRunActivity
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels) :
    totalActivity operations =
      ∑ key ∈ lineageRunKeys occurrences,
        lineageRunActivity occurrences key := by
  rw [sum_lineageRunActivity]
  exact history.occurrences_length.symm

/--
Every ordinary trace from an initial state has an exact lineage/run activity
grouping.
-/
theorem Trace.existsActivityGrouping
    {n : ℕ} {params : Parameters}
    {initial final : State n} {operations : List (Operation n)}
    (initialState : initial.Initial params)
    (trace : Trace params initial operations final) :
    ∃ (finalLabels : RootLabels)
        (occurrences : List (ActivityOccurrence n)),
      ActivityHistory params initial [] operations occurrences
          final finalLabels ∧
        finalLabels.length = final.blocks.length ∧
        (∀ occurrence ∈ occurrences,
          occurrence.root ∈ finalLabels) ∧
        totalActivity operations =
          ∑ key ∈ lineageRunKeys occurrences,
            lineageRunActivity occurrences key := by
  obtain ⟨finalLabels, lineageHistory, aligned⟩ :=
    HistoryTrace.lift_initial initialState trace
  obtain ⟨occurrences, activityHistory⟩ :=
    ActivityHistory.lift lineageHistory
  exact
    ⟨finalLabels, occurrences, activityHistory, aligned,
      activityHistory.occurrence_root_mem_finalLabels (by
        simp [initialState.2]),
      activityHistory.totalActivity_eq_sum_lineageRunActivity⟩

end Splay.Interface
