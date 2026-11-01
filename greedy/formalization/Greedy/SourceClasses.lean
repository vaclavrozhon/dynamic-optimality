import Greedy.SourceCensus

/-! Physical source-instance classes agree with the literal atomic partition. -/

namespace Greedy.SourceCensus

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open scoped BigOperators

noncomputable local instance : DecidableEq Frozen := Classical.decEq _
attribute [local instance] Classical.propDecidable

def SameBlockKeys {n : ℕ} (states : HeapSides n) (source : External n) (edge : ℕ × ℕ) : Prop :=
  ∃ side block, block ∈ (states source side).shrinking ∧ edge.1 ∈ blockKeys block ∧ edge.2 ∈ blockKeys block

theorem sameBlock_keys {n : ℕ} (states : HeapSides n) (source : External n) (event : External n × External n) :
    AccessTrace.SameBlock states source event ↔ SameBlockKeys states source (eventKeys event) := by
  constructor
  · rintro ⟨side, block, member, winner, winnerMem, loser, loserMem, winnerKey, loserKey⟩
    exact ⟨side, block, member, List.mem_map.mpr ⟨winner, winnerMem, winnerKey⟩,
      List.mem_map.mpr ⟨loser, loserMem, loserKey⟩⟩
  · rintro ⟨side, block, member, winner, loser⟩
    obtain ⟨winner, winnerMem, winnerKey⟩ := List.mem_map.mp winner
    obtain ⟨loser, loserMem, loserKey⟩ := List.mem_map.mp loser
    exact ⟨side, block, member, winner, winnerMem, loser, loserMem, winnerKey, loserKey⟩

theorem key_side_unique {n : ℕ} (states : HeapSides n) (source : External n)
    (valid : ∀ side, Valid source.val side (states source side))
    (firstSide secondSide : Bool) (first second : Frozen)
    (firstMem : first ∈ (states source firstSide).shrinking) (secondMem : second ∈ (states source secondSide).shrinking)
    (key : ℕ) (firstKey : key ∈ blockKeys first) (secondKey : key ∈ blockKeys second) : firstSide = secondSide := by
  obtain ⟨a, aMem, aKey⟩ := List.mem_map.mp firstKey
  obtain ⟨b, bMem, bKey⟩ := List.mem_map.mp secondKey
  have firstPosition := (valid firstSide).2.1 a (ClosedFamilies.frozen_entry_mem _ first firstMem a aMem)
  have secondPosition := (valid secondSide).2.1 b (ClosedFamilies.frozen_entry_mem _ second secondMem b bMem)
  cases firstSide <;> cases secondSide <;> simp only [onSide, Bool.false_eq_true, if_false, if_true] at firstPosition secondPosition ⊢ <;> omega

theorem sameBlock_iff_containing {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (loser : ℕ) (loserMem : loser ∈ atoms tree) (winner : ℕ)
    (block : Frozen) (member : block ∈ (states source side).shrinking) (contains : record loser ∈ blockKeys block) :
    SameBlockKeys states source (winner, record loser) ↔ winner ∈ blockKeys block := by
  constructor
  · rintro ⟨otherSide, other, otherMem, winnerKey, loserKey⟩
    have sideEq := key_side_unique states source valid otherSide side other block otherMem member _ loserKey contains
    subst otherSide
    have equal := unique_block view ids loser loserMem other block otherMem member loserKey contains
    exact equal ▸ winnerKey
  · intro winnerKey
    exact ⟨side, block, member, winnerKey, contains⟩

theorem sum_boundary_value {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (loser : ℕ) (loserMem : loser ∈ atoms tree) (winner : ℕ) (value : ℤ) :
    (∑ block ∈ (states source side).shrinking.toFinset,
      if record loser ∈ blockKeys block ∧ winner ∉ blockKeys block then value else 0) =
      if SameBlockKeys states source (winner, record loser) then 0 else value := by
  classical
  obtain ⟨block, member, contains⟩ := view.covered loser loserMem
  rw [Finset.sum_eq_single block]
  · have same := sameBlock_iff_containing states source side valid view ids loser loserMem winner block member contains
    simp only [contains, true_and, same]
    split_ifs <;> simp_all
  · intro other otherMem different
    apply if_neg
    intro both
    exact different (unique_block view ids loser loserMem other block (List.mem_toFinset.mp otherMem) member both.1 contains)
  · intro absent
    exact False.elim (absent (List.mem_toFinset.mpr member))

theorem boundary_sum {n lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} (states : HeapSides n) (source : External n) (side : Bool)
    (valid : ∀ direction, Valid source.val direction (states source direction))
    (view : SideView rank initial record tree (states source side))
    (ids : ((states source side).shrinking.map Frozen.id).Nodup)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) :
    (∑ block ∈ (states source side).shrinking.toFinset, DepartureAmounts.amount .boundary rank initial record owner tree block) =
      ∑ i : Fin (schedule owner tree).length,
        if SameBlockKeys states source (record ((schedule owner tree).get i).1, record ((schedule owner tree).get i).2) then 0 else
          if initial (record ((schedule owner tree).get i).2) ≤ DepartureCells.newLabel rank record ((schedule owner tree).get i) then 1 else 0 := by
  classical
  simp only [DepartureAmounts.amount, DepartureAmounts.cells, DepartureCells.boundary, DepartureAmounts.weight, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have member := (schedule_run (rank ∘ record) owner tree projection localOwners).event_members _ (List.get_mem _ i)
  by_cases nondrop : initial (record ((schedule owner tree).get i).2) ≤ DepartureCells.newLabel rank record ((schedule owner tree).get i)
  · simpa only [nondrop, and_true, if_true] using sum_boundary_value states source side valid view ids _ member.2
      (record ((schedule owner tree).get i).1) 1
  · simp only [nondrop, and_false, if_false, Finset.sum_const_zero, ite_self]

end Greedy.SourceCensus
