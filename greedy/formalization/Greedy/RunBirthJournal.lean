import Greedy.ExecutionRun
import Greedy.RunJournal

/-!
The finite registry contains only initial instances and actual births.
Reserved allocator names are not charged. Every source instance in the
literal execution belongs to this registry.
-/

namespace Greedy.RunBirthJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.ComparatorOuter FreshRecanonicalization

theorem refinement_support {n count : ℕ} (comparator : BST 0 n) (reader : Reader n)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator reader count first last births) :
    SupportsIds first.states last.states births := by
  induction execution with
  | nil => exact supportsIds_refl _
  | @cons count depth first last middle births rotation rest ih =>
      let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
      let result := FreshRecanonicalization.allocate comparator middle ports (reader first.clock) first.next first.states
      have head := reparentSelected_id_support comparator middle result.names result.names result.paidNames result.makeEntry ports first.states
      rw [FreshRecanonicalization.allocate_eq] at head
      exact supportsIds_trans head ih

theorem rotation_support {n depth : ℕ} (before : Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (K : ℤ) (data : Execution.RotationData before after rotation K) :
    SupportsIds before.blocks data.state.blocks data.journal := by
  let input := comparatorInput rotation
  let plan := rotationPlan input.step before.refined.tree
  let result := FreshComparator.allocate rotation before.refined.tree (Execution.entryReader after K before.clock) before.next before.blocks
  have head := executeComparatorPlan_id_support input.profile before.refined.tree plan
    result.families result.ids result.bulkNames result.paidNames result.makeEntry before.blocks
  dsimp only [result, FreshComparator.allocate] at head
  rw [allocateComparatorPlan_eq input.profile before.refined.tree plan
    (Execution.entryReader after K before.clock) before.next before.blocks] at head
  exact supportsIds_trans head (refinement_support after (Execution.entryReader after K) data.executed)

noncomputable def accessBirths {n : ℕ} (before : Execution.State n) (request : Fin n) : List ℕ :=
  conversionIds (rootNames (Execution.source request) before.next false) (before.blocks (Execution.source request) false) ++
    conversionIds (rootNames (Execution.source request) before.next true) (before.blocks (Execution.source request) true)

theorem accessBirths_length {n : ℕ} (before : Execution.State n) (request : Fin n) :
    (accessBirths before request).length = rootConversionBirths (Execution.source request) before.blocks := by
  simp only [accessBirths, List.length_append, conversionIds_length, rootConversionBirths]

theorem preparation_support {n : ℕ} (before : Execution.State n) (request : Fin n) :
    SupportsIds before.blocks (RunJournal.prepared before request) (accessBirths before request) := by
  intro id ⟨owner, side, member⟩
  change id ∈ liveIds ((convertHeap before.comparator.externalDepth
    (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks).1 owner side) at member
  rw [← convertRoot_eq_convertHeap] at member
  by_cases selected : owner = Execution.source request
  · subst owner
    simp only [convertRoot, if_true] at member
    rcases conversion_id_support _ _ _ _ _ id member with old | born
    · exact Or.inl ⟨_, side, old⟩
    · right
      cases side
      · exact List.mem_append_left _ born
      · exact List.mem_append_right _ born
  · exact Or.inl ⟨owner, side, by simpa only [convertRoot, if_neg selected] using member⟩

theorem access_support {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree (Execution.afterRefinement before request).tree decomposition) :
    SupportsIds before.blocks (Execution.afterAccess before request K decomposition data).blocks (accessBirths before request) := by
  intro id ⟨owner, side, member⟩
  change id ∈ liveIds (runLinks _ _ _ _ _ _ owner side) at member
  rw [runLinks_liveIds] at member
  exact preparation_support before request id ⟨owner, side, member⟩

noncomputable def journal {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)} :
    Execution.Run K first last requests → List ℕ
  | .done _ => []
  | .rotate _ data _ rest => data.journal ++ journal rest
  | .access (first := first) request _ _ _ _ rest => accessBirths first request ++ journal rest

theorem journal_length {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) : (journal execution).length = execution.births := by
  induction execution with
  | done => rfl
  | rotate _ _ _ rest ih => simp only [journal, List.length_append, ih, Execution.Run.births]
  | access _ _ _ _ _ rest ih => simp only [journal, List.length_append, accessBirths_length, ih, Execution.Run.births]

def Covered {n : ℕ} (names : Finset ℕ) (states : HeapSides n) : Prop := ∀ id, LiveId states id → id ∈ names

theorem Covered.mono {n : ℕ} {first second : Finset ℕ} {states : HeapSides n}
    (covered : Covered first states) (subset : first ⊆ second) : Covered second states := fun id member => subset (covered id member)

theorem Covered.support {n : ℕ} {names : Finset ℕ} {before after : HeapSides n} {births : List ℕ}
    (covered : Covered names before) (support : SupportsIds before after births) : Covered (names ∪ births.toFinset) after := by
  intro id member
  rcases support id member with old | born
  · exact Finset.mem_union_left _ (covered id old)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr born)

def AllSourcesCovered {n : ℕ} (names : Finset ℕ) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} : Execution.Run K first last requests → Prop
  | .done state => Covered names state.blocks
  | .rotate (first := first) _ _ _ rest => Covered names first.blocks ∧ AllSourcesCovered names rest
  | .access (first := first) request _ _ _ _ rest =>
      Covered names first.blocks ∧ Covered names (RunJournal.prepared first request) ∧ AllSourcesCovered names rest

theorem all_sources_covered {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (names : Finset ℕ) (covered : Covered names first.blocks) :
    AllSourcesCovered (names ∪ (journal execution).toFinset) execution := by
  induction execution generalizing names with
  | done => simpa only [journal, List.toFinset_nil, Finset.union_empty, AllSourcesCovered] using covered
  | @rotate first last after depth requests rotation data valid rest ih =>
      have tail := ih (names ∪ data.journal.toFinset) (covered.support (rotation_support first after rotation K data))
      refine ⟨covered.mono (Finset.subset_union_left), ?_⟩
      simpa only [journal, List.toFinset_append, Finset.union_assoc] using tail
  | @access first last requests request root decomposition data valid rest ih =>
      have tail := ih (names ∪ (accessBirths first request).toFinset) (covered.support (access_support first request K decomposition data))
      refine ⟨covered.mono Finset.subset_union_left, ?_, ?_⟩
      · apply (covered.support (preparation_support first request)).mono
        simp only [journal, List.toFinset_append]
        exact Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_left
      · simpa only [journal, List.toFinset_append, Finset.union_assoc] using tail

noncomputable def registry {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) : Finset ℕ := Finset.range first.next ∪ (journal execution).toFinset

theorem registry_card {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) : (registry execution).card ≤ first.next + execution.births := by
  have union := Finset.card_union_le (Finset.range first.next) (journal execution).toFinset
  have size := List.toFinset_card_le (journal execution)
  rw [journal_length] at size
  simp only [registry, Finset.card_range] at union ⊢
  omega

theorem registry_covers {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid) : AllSourcesCovered (registry execution) execution := by
  apply all_sources_covered
  intro id ⟨owner, side, member⟩
  exact Finset.mem_range.mpr (valid.2.2.1.below (encode n (owner, side)) id (by simpa only [table, Equiv.symm_apply_apply] using member))

end Greedy.RunBirthJournal
