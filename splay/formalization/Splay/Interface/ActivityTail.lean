import Splay.Interface.Activity

namespace Splay.Interface

open scoped BigOperators

/-- Activity contributed by passes whose inherited pre-pass count is at least
the selected global threshold. -/
def tailActivity {n : ℕ}
    (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) : ℕ :=
  (occurrences.filter fun occurrence =>
    decide (threshold ≤ occurrence.passCount)).length

/-- The actual lineage keys that lie in the high-pass-count tail. -/
def tailLineageRunKeys {n : ℕ}
    (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) : Finset LineageRunKey :=
  (lineageRunKeys occurrences).filter fun key =>
    threshold ≤ key.2

/-- Roots that actually carry at least one high-count activity fiber. -/
def tailRoots {n : ℕ}
    (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) : Finset RootId :=
  (tailLineageRunKeys occurrences threshold).image Prod.fst

/-- High-count activity belonging to one fixed root lineage. -/
def rootTailActivity {n : ℕ}
    (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) (root : RootId) : ℕ :=
  ∑ key ∈ tailLineageRunKeys occurrences threshold with
      key.1 = root,
    lineageRunActivity occurrences key

/-- Direct occurrence-list form of one root's high-count activity. -/
def rootTailCount {n : ℕ}
    (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) (root : RootId) : ℕ :=
  (occurrences.filter fun occurrence =>
    decide
      (occurrence.root = root ∧
        threshold ≤ occurrence.passCount)).length

private theorem lineageRunKeys_filter_passCount
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) :
    lineageRunKeys
        (occurrences.filter fun occurrence =>
          decide (threshold ≤ occurrence.passCount)) =
      tailLineageRunKeys occurrences threshold := by
  ext key
  simp only [lineageRunKeys, tailLineageRunKeys,
    Finset.mem_filter, List.mem_toFinset, List.mem_map,
    List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨occurrence, ⟨member, high⟩, keyEq⟩
    subst key
    exact
      ⟨⟨occurrence, member, rfl⟩, high⟩
  · rintro ⟨⟨occurrence, member, keyEq⟩, high⟩
    subst key
    exact
      ⟨occurrence, ⟨member, high⟩, rfl⟩

private theorem lineageRunActivity_filter_passCount
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) (key : LineageRunKey)
    (high : threshold ≤ key.2) :
    lineageRunActivity
        (occurrences.filter fun occurrence =>
          decide (threshold ≤ occurrence.passCount)) key =
      lineageRunActivity occurrences key := by
  unfold lineageRunActivity
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro occurrence _member
  by_cases same : occurrence.key = key
  · have occurrenceHigh :
        threshold ≤ occurrence.passCount := by
      simpa [ActivityOccurrence.key] using
        (show threshold ≤ occurrence.key.2 by
          simpa [same] using high)
    simp [same, occurrenceHigh]
  · simp [same]

/--
Exact grouping of insignificant activity by its actual `(root, passCount)`
fibers.  This is the finite aggregation identity needed when one decay tail
is constructed for each root lineage.
-/
theorem tailActivity_eq_sum_lineageRunActivity
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) :
    tailActivity occurrences threshold =
      ∑ key ∈ tailLineageRunKeys occurrences threshold,
        lineageRunActivity occurrences key := by
  let tail :=
    occurrences.filter fun occurrence =>
      decide (threshold ≤ occurrence.passCount)
  have grouped := sum_lineageRunActivity tail
  rw [lineageRunKeys_filter_passCount] at grouped
  have replace :
      (∑ key ∈ tailLineageRunKeys occurrences threshold,
          lineageRunActivity tail key) =
        ∑ key ∈ tailLineageRunKeys occurrences threshold,
          lineageRunActivity occurrences key := by
    apply Finset.sum_congr rfl
    intro key keyMem
    have high :
        threshold ≤ key.2 :=
      (Finset.mem_filter.mp keyMem).2
    exact
      lineageRunActivity_filter_passCount
        occurrences threshold key high
  rw [replace] at grouped
  exact grouped.symm

/-- The high-count key sum can equivalently be grouped first by root. -/
theorem tailActivity_eq_sum_rootTailActivity
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) :
    tailActivity occurrences threshold =
      ∑ root ∈ tailRoots occurrences threshold,
        rootTailActivity occurrences threshold root := by
  rw [tailActivity_eq_sum_lineageRunActivity]
  symm
  exact
    Finset.sum_fiberwise_of_maps_to
      (s := tailLineageRunKeys occurrences threshold)
      (t := tailRoots occurrences threshold)
      (g := Prod.fst)
      (fun key keyMem =>
        Finset.mem_image.mpr ⟨key, keyMem, rfl⟩)
      (fun key => lineageRunActivity occurrences key)

/-- The fiber sum for one root is exactly the direct filtered occurrence
count. -/
theorem rootTailActivity_eq_rootTailCount
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) (root : RootId) :
    rootTailActivity occurrences threshold root =
      rootTailCount occurrences threshold root := by
  let selected :=
    occurrences.filter fun occurrence =>
      decide
        (occurrence.root = root ∧
          threshold ≤ occurrence.passCount)
  have selectedKeys :
      lineageRunKeys selected =
        (tailLineageRunKeys occurrences threshold).filter
          fun key => key.1 = root := by
    ext key
    simp only [selected, lineageRunKeys, tailLineageRunKeys,
      List.mem_toFinset, List.mem_map, List.mem_filter,
      Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨occurrence, ⟨member, rootEq, high⟩, keyEq⟩
      subst key
      exact
        ⟨⟨⟨occurrence, member, rfl⟩, high⟩,
          rootEq⟩
    · rintro
        ⟨⟨⟨occurrence, member, keyEq⟩, high⟩, rootEq⟩
      subst key
      exact
        ⟨occurrence, ⟨member, rootEq, high⟩, rfl⟩
  have selectedActivity
      (key : LineageRunKey)
      (keyMem :
        key ∈
          (tailLineageRunKeys occurrences threshold).filter
            fun candidate => candidate.1 = root) :
      lineageRunActivity selected key =
        lineageRunActivity occurrences key := by
    have filtered := Finset.mem_filter.mp keyMem
    have high := (Finset.mem_filter.mp filtered.1).2
    have rootEq := filtered.2
    unfold lineageRunActivity
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro occurrence _member
    by_cases same : occurrence.key = key
    · have occurrenceRoot : occurrence.root = root := by
        calc
          occurrence.root = occurrence.key.1 := rfl
          _ = key.1 := congrArg Prod.fst same
          _ = root := rootEq
      have occurrenceHigh :
          threshold ≤ occurrence.passCount := by
        have countEq :
            occurrence.passCount = key.2 := by
          exact congrArg Prod.snd same
        simpa [countEq] using high
      simp [same, occurrenceRoot, occurrenceHigh]
    · simp [same]
  have grouped := sum_lineageRunActivity selected
  rw [selectedKeys] at grouped
  have replace :
      (∑ key ∈
          (tailLineageRunKeys occurrences threshold).filter
            (fun candidate => candidate.1 = root),
          lineageRunActivity selected key) =
        ∑ key ∈
          (tailLineageRunKeys occurrences threshold).filter
            (fun candidate => candidate.1 = root),
          lineageRunActivity occurrences key := by
    apply Finset.sum_congr rfl
    intro key keyMem
    exact selectedActivity key keyMem
  rw [replace] at grouped
  change
    (∑ key ∈ tailLineageRunKeys occurrences threshold with
        key.1 = root,
      lineageRunActivity occurrences key) =
      selected.length
  exact grouped

/-- The tail activity is bounded by total occurrence activity. -/
theorem tailActivity_le_length
    {n : ℕ} (occurrences : List (ActivityOccurrence n))
    (threshold : ℕ) :
    tailActivity occurrences threshold ≤ occurrences.length := by
  exact List.length_filter_le _ _

end Splay.Interface
