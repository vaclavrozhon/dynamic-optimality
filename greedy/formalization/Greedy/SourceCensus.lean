import Greedy.DepartureAccess

/-! Every actual source record belongs to exactly one literal frozen instance. -/

namespace Greedy.SourceCensus

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open scoped BigOperators

noncomputable local instance : DecidableEq Frozen := Classical.decEq _

theorem unique_block {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (ids : (state.shrinking.map Frozen.id).Nodup) (key : ℕ) (keyMem : key ∈ atoms tree)
    (first second : Frozen) (firstMem : first ∈ state.shrinking) (secondMem : second ∈ state.shrinking)
    (firstKey : record key ∈ blockKeys first) (secondKey : record key ∈ blockKeys second) : first = second := by
  have bounds := (atoms_mem_iff tree key).mp keyMem
  have same := ((view.matching key bounds.1 bounds.2 first firstMem).mpr firstKey).symm.trans
    ((view.matching key bounds.1 bounds.2 second secondMem).mpr secondKey)
  exact List.inj_on_of_nodup_map ids firstMem secondMem same

theorem sum_containing {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (ids : (state.shrinking.map Frozen.id).Nodup) (key : ℕ) (keyMem : key ∈ atoms tree) (value : ℤ) :
    (∑ block ∈ state.shrinking.toFinset, if record key ∈ blockKeys block then value else 0) = value := by
  classical
  obtain ⟨block, member, contains⟩ := view.covered key keyMem
  rw [Finset.sum_eq_single block]
  · exact if_pos contains
  · intro other otherMem different
    apply if_neg
    intro otherKey
    exact different (unique_block view ids key keyMem other block (List.mem_toFinset.mp otherMem) member otherKey contains)
  · intro absent
    exact False.elim (absent (List.mem_toFinset.mpr member))

theorem sum_pieces {n : ℕ} (states : HeapSides n) (source : External n) (weight : Bool × Frozen → ℤ) :
    (∑ piece ∈ CreatorPhase.pieces states source, weight piece) =
      (∑ block ∈ (states source true).shrinking.toFinset, weight (true, block)) +
      (∑ block ∈ (states source false).shrinking.toFinset, weight (false, block)) := by
  classical
  have disjoint : Disjoint (((states source true).shrinking.map (fun block => (true, block))).toFinset)
      (((states source false).shrinking.map (fun block => (false, block))).toFinset) := by
    apply Finset.disjoint_left.mpr
    intro piece first second
    obtain ⟨a, _, firstEq⟩ := List.mem_map.mp (List.mem_toFinset.mp first)
    obtain ⟨b, _, secondEq⟩ := List.mem_map.mp (List.mem_toFinset.mp second)
    have different := congrArg Prod.fst (firstEq.trans secondEq.symm)
    cases different
  have mapped (side : Bool) :
      ((states source side).shrinking.map (fun block => (side, block))).toFinset =
        (states source side).shrinking.toFinset.image (fun block => (side, block)) := by
    ext piece
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  simp only [CreatorPhase.pieces, List.toFinset_append]
  rw [Finset.sum_union disjoint]
  simp only [mapped]
  rw [Finset.sum_image, Finset.sum_image]
  · intro a _ b _ same
    exact congrArg Prod.snd same
  · intro a _ b _ same
    exact congrArg Prod.snd same

theorem increase_sum {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (ids : (state.shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) :
    (∑ block ∈ state.shrinking.toFinset, DepartureAmounts.amount .increase rank initial record owner tree block) =
      ∑ i : Fin (schedule owner tree).length,
        DepartureAmounts.weight .increase rank initial record ((schedule owner tree).get i) := by
  classical
  simp only [DepartureAmounts.amount, DepartureAmounts.cells, DepartureCells.positive, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have member := (schedule_run (rank ∘ record) owner tree projection localOwners).event_members _ (List.get_mem _ i)
  by_cases increase : initial (record ((schedule owner tree).get i).2) < DepartureCells.newLabel rank record ((schedule owner tree).get i)
  · simpa only [increase, and_true] using sum_containing view ids _ member.2
      (DepartureAmounts.weight .increase rank initial record ((schedule owner tree).get i))
  · have zero : DepartureAmounts.weight .increase rank initial record ((schedule owner tree).get i) = 0 := by
      simp only [DepartureAmounts.weight]
      omega
    simp only [increase, and_false, if_false, zero, Finset.sum_const_zero]

end Greedy.SourceCensus
