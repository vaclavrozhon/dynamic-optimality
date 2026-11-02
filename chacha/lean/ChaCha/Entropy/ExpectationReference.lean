import ChaCha.Entropy.ExpectationProjection

/-!
# Relating random token switches to the repository's primary counter

Child counters ignore all requests outside their leaf sets. Thus their
expectations can be taken on the original full random word, avoiding any
assumption about the distribution of a recursively filtered word.
-/

namespace ChaCha.Entropy

open PreferredProjection

private theorem filterMap_filter_kept {α β : Type*} (word : List α)
    (keep : α → Bool) (classify : α → Option β)
    (kept : ∀ key, classify key ≠ none → keep key = true) :
    (word.filter keep).filterMap classify = word.filterMap classify := by
  induction word with
  | nil => rfl
  | cons key word ih =>
    by_cases present : keep key = true
    · rw [List.filter_cons,if_pos present,List.filterMap_cons,List.filterMap_cons,ih]
    · have missing : classify key = none := by
        by_contra nonempty
        exact present (kept key nonempty)
      simp [present,missing,ih]

private theorem filter_filter_kept {α : Type*} (word : List α) (keep choose : α → Bool)
    (kept : ∀ key, choose key = true → keep key = true) :
    (word.filter keep).filter choose = word.filter choose := by
  have predicates : (fun key => choose key && keep key) = choose := by
    funext key
    by_cases selected : choose key = true
    · simp [selected,kept key selected]
    · simp [selected]
  simp only [List.filter_filter,predicates]

/-- The reference's original exact counter is unchanged by dropping requests
outside its leaf set. The preserved predicate may retain additional keys. -/
theorem primary_filter_kept (reference : PrefRouter Int) (word : List Int) (keep : Int → Bool)
    (kept : ∀ key ∈ reference.leaves, keep key = true) :
    reference.primaryWilber (word.filter keep) = reference.primaryWilber word := by
  cases reference with
  | leaf => rfl
  | fork preference left right =>
    have branch : PrefRouter.branchWord left.leaves right.leaves (word.filter keep) =
        PrefRouter.branchWord left.leaves right.leaves word := by
      apply filterMap_filter_kept
      intro key present
      by_cases low : key ∈ left.leaves
      · exact kept key (List.mem_append.mpr (Or.inl low))
      · by_cases high : key ∈ right.leaves
        · exact kept key (List.mem_append.mpr (Or.inr high))
        · simp [low,high] at present
    have low : PrefRouter.leftWord left.leaves (word.filter keep) = PrefRouter.leftWord left.leaves word := by
      apply filter_filter_kept
      intro key present
      exact kept key (List.mem_append.mpr (Or.inl (of_decide_eq_true present)))
    have high : PrefRouter.rightWord left.leaves right.leaves (word.filter keep) =
        PrefRouter.rightWord left.leaves right.leaves word := by
      apply filter_filter_kept
      intro key present
      exact kept key (List.mem_append.mpr (Or.inr (of_decide_eq_true present).2))
    simp only [PrefRouter.primaryWilber,branch,low,high]

theorem primary_fork_unfiltered (preference : Bool) (left right : PrefRouter Int) (word : List Int)
    (disjoint : List.Disjoint left.leaves right.leaves) :
    (PrefRouter.fork preference left right).primaryWilber word =
      ChaCha.alternations (PrefRouter.branchWord left.leaves right.leaves word) +
        left.primaryWilber word + right.primaryWilber word := by
  have low := primary_filter_kept left word (fun key => decide (key ∈ left.leaves))
    (by intro key present; exact decide_eq_true present)
  have high := primary_filter_kept right word (fun key => decide (key ∉ left.leaves ∧ key ∈ right.leaves))
    (by
      intro key present
      exact decide_eq_true ⟨fun low => disjoint low present,present⟩)
  simp only [PrefRouter.primaryWilber,PrefRouter.leftWord,PrefRouter.rightWord,low,high]

private theorem filter_union_length (word : List Int) (left right : Int → Prop)
    [DecidablePred left] [DecidablePred right] (disjoint : ∀ key, ¬ (left key ∧ right key)) :
    (word.filter (fun key => decide (left key ∨ right key))).length =
      (word.filter (fun key => decide (left key))).length +
      (word.filter (fun key => decide (right key))).length := by
  induction word with
  | nil => rfl
  | cons key word ih =>
    simp only [Bool.decide_or] at ih
    by_cases low : left key <;> by_cases high : right key
    · exact (disjoint key ⟨low,high⟩).elim
    · simp [low,high,ih,Nat.add_assoc,Nat.add_comm]
    · simp [low,high,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [low,high,ih]

/-- A nodup list of keys counts each histogram bin once. -/
theorem weight_count (base keys : List Int) (nodup : keys.Nodup) :
    weight base.count keys = (base.filter (fun key => decide (key ∈ keys))).length := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp nodup
    have split := filter_union_length base (fun other => other=key) (fun other => other∈keys)
      (by rintro other ⟨rfl,present⟩; exact absent present)
    rw [weight_cons,ih tail,List.count_eq_length_filter]
    simpa only [List.mem_cons,Bool.beq_eq_decide_eq] using split.symm

private def branchClass (left right : List Int) (key : Int) : Option Bool :=
  if key ∈ left then some false else if key ∈ right then some true else none

theorem branch_switch_expectation (base left right : List Int)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup) (disjoint : List.Disjoint left right) :
    shuffleExpectation base (fun word => (ChaCha.alternations (PrefRouter.branchWord left right word) : ℝ)) =
      2 * (weight base.count left : ℝ) * (weight base.count right : ℝ) /
        ((weight base.count left : ℝ)+(weight base.count right : ℝ)) := by
  let classify : Fin base.length → Option Bool := branchClass left right ∘ base.get
  have first : classCount classify false = weight base.count left := by
    rw [weight_count base left leftNodup,← token_count base (fun key => decide (key ∈ left))]
    unfold classCount
    congr 1
    ext token
    by_cases low : base.get token ∈ left <;>
      by_cases high : base.get token ∈ right <;> simp [classify,branchClass,low,high]
  have second : classCount classify true = weight base.count right := by
    rw [weight_count base right rightNodup,← token_count base (fun key => decide (key ∈ right))]
    unfold classCount
    congr 1
    ext token
    by_cases low : base.get token ∈ left <;> by_cases high : base.get token ∈ right
    · exact (disjoint low high).elim
    · simp only [List.get_eq_getElem] at low high
      simp [classify,branchClass,low,high]
    · simp only [List.get_eq_getElem] at low high
      simp [classify,branchClass,low,high]
    · simp only [List.get_eq_getElem] at low high
      simp [classify,branchClass,low,high]
  have projected (sample : ShuffleSample base) :
      PrefRouter.branchWord left right (sampleWord base sample) =
        ((List.finRange base.length).map sample).filterMap classify := by
    simp only [PrefRouter.branchWord,sampleWord,List.ofFn_eq_map,List.filterMap_map,Function.comp_def]
    rfl
  unfold shuffleExpectation
  simp_rw [projected]
  rw [classified_switch_expectation,first,second]

/-- The expected *actual* primary counter of an arbitrary leaf-distinct
reference, in the explicit fixed-histogram probability space. -/
theorem primary_expectation (base : List Int) (reference : PrefRouter Int)
    (nodup : reference.leaves.Nodup) :
    shuffleExpectation base (fun word => (reference.primaryWilber word : ℝ)) =
      alternationMass base.count reference := by
  induction reference with
  | leaf => simp [shuffleExpectation,PrefRouter.primaryWilber,alternationMass]
  | fork preference left right ihl ihr =>
    obtain ⟨leftNodup,rightNodup,separate⟩ := List.nodup_append.mp nodup
    have disjoint : List.Disjoint left.leaves right.leaves := by
      intro key low high
      exact separate key low key high rfl
    have counter (word : List Int) := primary_fork_unfiltered preference left right word disjoint
    have branch := branch_switch_expectation base left.leaves right.leaves leftNodup rightNodup disjoint
    simp only [shuffleExpectation] at ihl ihr branch ⊢
    simp_rw [counter,Nat.cast_add]
    rw [uniformMean_add,uniformMean_add,branch,ihl leftNodup,ihr rightNodup]
    rfl

end ChaCha.Entropy
