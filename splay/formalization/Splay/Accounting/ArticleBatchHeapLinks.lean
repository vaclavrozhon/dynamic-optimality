import Splay.Accounting.ArticleSelectionHeapLinks

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- Heap links enumerated by a list of joint first/second selections. -/
noncomputable def pairedSelectionHeapLinks {n : ℕ}
    (selections : List (List (External n) × List (External n))) : Finset (External n × External n) :=
  selections.toFinset.biUnion fun pair => selectionHeapLinks pair.1 ∪ selectionHeapLinks pair.2

@[simp]
theorem mem_pairedSelectionHeapLinks {n : ℕ} (selections : List (List (External n) × List (External n)))
    (link : External n × External n) :
    link ∈ pairedSelectionHeapLinks selections ↔
      ∃ pair ∈ selections, link ∈ selectionHeapLinks pair.1 ∪ selectionHeapLinks pair.2 := by
  simp [pairedSelectionHeapLinks]

theorem pairedSelectionHeapLinks_zip {n : ℕ} (first second : List (List (External n)))
    (lengthEq : first.length = second.length) :
    pairedSelectionHeapLinks (first.zip second) = selectionListHeapLinks first ∪ selectionListHeapLinks second := by
  induction first generalizing second with
  | nil =>
      have empty : second = [] := List.length_eq_zero_iff.mp lengthEq.symm
      subst second
      simp [pairedSelectionHeapLinks]
  | cons first rest ih =>
      cases second with
      | nil => simp at lengthEq
      | cons second tail =>
          have tailEq : rest.length = tail.length := by simpa using lengthEq
          simp only [List.zip_cons_cons]
          have consEq : pairedSelectionHeapLinks ((first, second) :: rest.zip tail) =
              (selectionHeapLinks first ∪ selectionHeapLinks second) ∪ pairedSelectionHeapLinks (rest.zip tail) := by
            simp [pairedSelectionHeapLinks]
          rw [consEq, ih tail tailEq, selectionListHeapLinks_cons, selectionListHeapLinks_cons]
          ac_rfl

namespace ArticleRetainedPairingBatches

/-- The union of the two actual phase links in every retained article row. -/
noncomputable def heapLinks {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {bound : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before bound key groups) : Finset (External n × External n) :=
  batches.rows.toFinset.biUnion articleRowHeapLinks

@[simp]
theorem mem_heapLinks {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {bound : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before bound key groups) (link : External n × External n) :
    link ∈ batches.heapLinks ↔ ∃ row ∈ batches.rows, link ∈ articleRowHeapLinks row := by
  simp [heapLinks]

/-- Group alignment alone identifies the links of an arbitrary retained row
enumeration with a joint chronological selection of the same groups. -/
theorem heapLinks_eq_of_alignment {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {bound : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before bound key groups)
    {selections : List (List (External n) × List (External n))}
    (aligned : List.Forall₂ (SequentialPhaseSelectionAtDoubleGroup snapshot before bound key) groups selections) :
    batches.heapLinks = pairedSelectionHeapLinks selections := by
  ext link
  rw [mem_heapLinks, mem_pairedSelectionHeapLinks]
  constructor
  · rintro ⟨row, rowMember, linkMember⟩
    have groupMember : row.1 ∈ groups := batches.groups_perm.mem_iff.mp (List.mem_map.mpr ⟨row, rowMember, rfl⟩)
    obtain ⟨pair, pairMember, pairAligned⟩ := forall₂_exists_right_of_mem_left aligned groupMember
    have equal := (batches.aligned row rowMember).heapLinks_unique pairAligned
    exact ⟨pair, pairMember, equal ▸ linkMember⟩
  · rintro ⟨pair, pairMember, linkMember⟩
    obtain ⟨group, groupMember, pairAligned⟩ := forall₂_exists_right_of_mem_left aligned.flip pairMember
    have rowGroup : group ∈ batches.rows.map Prod.fst := batches.groups_perm.mem_iff.mpr groupMember
    obtain ⟨row, rowMember, equal⟩ := List.mem_map.mp rowGroup
    have rowAligned := batches.aligned row rowMember
    rw [equal] at rowAligned
    have linkEq := SequentialPhaseSelectionAtDoubleGroup.heapLinks_unique pairAligned rowAligned
    refine ⟨row, rowMember, ?_⟩
    change link ∈ selectionHeapLinks row.2.1 ∪ selectionHeapLinks row.2.2
    rw [← linkEq]
    exact linkMember

/-- The complete article batch represents exactly the heap links of the
actual request transcript. This also covers either permissible phase order
when the middle candidate wins. -/
theorem heapLinks_eq_transcript {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n} {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key (zigZigDoubleGroupIndices kinds 0))
    (key_lt_n : key < n) (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    batches.heapLinks = transcriptPairingLinks snapshot transcript := by
  obtain ⟨first, second, joint, _, _, _, _⟩ :=
    transcript.exists_bothPhaseSelections_atDoubleGroups (Nat.le_refl n) key_lt_n rankZero
  rw [batches.heapLinks_eq_of_alignment
    (joint.forall₂_sequential_atDoubleGroups (Nat.le_refl n) key_lt_n rankZero)]
  rw [pairedSelectionHeapLinks_zip _ _ joint.forall₂_sequential.length_eq]
  exact joint.heapLinks_eq.symm

end ArticleRetainedPairingBatches

end Splay.Accounting
