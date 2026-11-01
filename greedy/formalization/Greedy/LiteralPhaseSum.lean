import Greedy.SourceWeights
import Greedy.SourceCollapse

/-! Signed coefficients read directly from the literal frozen source entries. -/

namespace Greedy.CreatorPhase

open Splay.Tree GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest GreedyForest.Phase GreedyMerge.ActualBlockPartition
open GreedyMerge.AccessSourceAccounting GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open scoped BigOperators

noncomputable def weight (state : SideState) (block : Frozen) (record : ℕ → ℕ)
    (time : ℕ) (edge : ℕ × ℕ) : ℤ :=
  if record edge.1 ∈ blockKeys block ∧ record edge.2 ∈ blockKeys block then
    joinCoefficient (storedJoin state (record edge.1)) (storedJoin state (record edge.2)) time else 0

noncomputable def coefficient {lo hi : ℕ} (state : SideState) (block : Frozen)
    (record owner : ℕ → ℕ) (tree : BST lo hi) (time : ℕ) : ℤ :=
  ∑ edge ∈ (schedule owner tree).toFinset, weight state block record time edge

theorem weight_matches {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (block : Frozen) (member : block ∈ state.shrinking) (time : ℕ) (edge : ℕ × ℕ)
    (first : edge.1 ∈ atoms tree) (second : edge.2 ∈ atoms tree) :
    weight state block record time edge = SignedPhase.historyWeight
      (blockMembers tree view.partition.block block.id) (storedJoin state ∘ record) time edge := by
  have matching (atom : ℕ) (atomMem : atom ∈ atoms tree) :
      atom ∈ blockMembers tree view.partition.block block.id ↔ record atom ∈ blockKeys block := by
    have bounds := (atoms_mem_iff tree atom).mp atomMem
    simp only [blockMembers, Finset.mem_filter, List.mem_toFinset, atomMem, true_and]
    exact view.matching atom bounds.1 bounds.2 block member
  simp only [weight, SignedPhase.historyWeight, matching edge.1 first, matching edge.2 second, Function.comp_apply]

theorem coefficient_bound {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (source : ℕ) (side : Bool) (valid : Valid source side state)
    (recordMono : ∀ first ∈ atoms tree, ∀ second ∈ atoms tree, first ≤ second → record first ≤ record second)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (block : Frozen) (member : block ∈ state.shrinking)
    (history : ∃ orientation, HistMonotone orientation block.members) (time : ℕ) :
    |coefficient state block record owner tree time| ≤ 3 := by
  obtain ⟨geometry⟩ := SourceWeights.stored_signed_geometry view source side valid recordMono
    owner projection localOwners block member history time
  have equal : coefficient state block record owner tree time =
      ∑ edge ∈ (schedule owner tree).toFinset,
        SignedPhase.historyWeight (blockMembers tree view.partition.block block.id) (storedJoin state ∘ record) time edge := by
    apply Finset.sum_congr rfl
    intro edge edgeMem
    have geometric := (schedule_perm_edges (rank ∘ record) owner tree projection localOwners).mem_iff.mp
      (List.mem_toFinset.mp edgeMem)
    have bounds := edge_strict_rank_and_bounds (rank ∘ record) owner tree edge.1 edge.2 projection
      geometric
    exact weight_matches view block member time edge
      ((atoms_mem_iff tree edge.1).mpr ⟨bounds.1, bounds.2.1⟩)
      ((atoms_mem_iff tree edge.2).mpr ⟨bounds.2.2.1, bounds.2.2.2.1⟩)
  rw [equal]
  exact geometry.bound

theorem weight_nonzero_crosses (state : SideState) (block : Frozen) (record : ℕ → ℕ)
    (source : ℕ) (side : Bool) (valid : Valid source side state)
    (member : block ∈ state.shrinking) (time : ℕ) (edge : ℕ × ℕ)
    (nonzero : weight state block record time edge ≠ 0) :
    Straddles (fun joined => decide (time+1 ≤ joined)) (GreedyMerge.FrozenHistory.joins block) := by
  unfold weight at nonzero
  split_ifs at nonzero with both
  · obtain ⟨winner, winnerMem, winnerKey⟩ := List.mem_map.mp both.1
    obtain ⟨loser, loserMem, loserKey⟩ := List.mem_map.mp both.2
    rw [← winnerKey, ← loserKey, storedJoin_of_frozen state source side valid block member winner winnerMem,
      storedJoin_of_frozen state source side valid block member loser loserMem] at nonzero
    exact FamilyOrder.coefficient_straddles block winner loser time winnerMem loserMem nonzero
  · exact False.elim (nonzero rfl)

theorem coefficient_nonzero_crosses {lo hi : ℕ} (state : SideState) (block : Frozen)
    (record owner : ℕ → ℕ) (tree : BST lo hi) (source : ℕ) (side : Bool)
    (valid : Valid source side state) (member : block ∈ state.shrinking) (time : ℕ)
    (nonzero : coefficient state block record owner tree time ≠ 0) :
    Straddles (fun joined => decide (time+1 ≤ joined)) (GreedyMerge.FrozenHistory.joins block) := by
  obtain ⟨edge, _, edgeNonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact weight_nonzero_crosses state block record source side valid member time edge edgeNonzero

end Greedy.CreatorPhase
