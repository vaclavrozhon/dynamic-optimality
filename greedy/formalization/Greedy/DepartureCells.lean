import Greedy.AtomicDepartures

/-! Positive updates and nondropping boundary links from actual source entries. -/

namespace Greedy.DepartureCells

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualBlockPartition
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyForest.Phase
open scoped BigOperators

def newLabel (rank record : ℕ → ℕ) (edge : ℕ × ℕ) : ℤ :=
  contractedGap (rank (record edge.2) - rank (record edge.1))

noncomputable def positive (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (block : Frozen) : Finset (Fin events.length) :=
  Finset.univ.filter (fun i => record (events.get i).2 ∈ blockKeys block ∧
    initial (record (events.get i).2) < newLabel rank record (events.get i))

noncomputable def boundary (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (block : Frozen) : Finset (Fin events.length) :=
  Finset.univ.filter (fun i => record (events.get i).2 ∈ blockKeys block ∧
    record (events.get i).1 ∉ blockKeys block ∧
    initial (record (events.get i).2) ≤ newLabel rank record (events.get i))

theorem positive_loser (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (block : Frozen) (i : Fin events.length) (member : i ∈ positive rank initial record events block) :
    record (events.get i).2 ∈ ClosedInstances.keys block := List.mem_toFinset.mpr (Finset.mem_filter.mp member).2.1

theorem boundary_loser (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (block : Frozen) (i : Fin events.length) (member : i ∈ boundary rank initial record events block) :
    record (events.get i).2 ∈ ClosedInstances.keys block := List.mem_toFinset.mpr (Finset.mem_filter.mp member).2.1

theorem positive_eq {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : Frozen) (member : block ∈ state.shrinking) :
    positive rank initial record (schedule owner tree) block =
      blockPositive (rank ∘ record) (initial ∘ record) (schedule owner tree) view.partition.block block.id := by
  ext i
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have endpoint := run.event_members _ (List.get_mem _ i)
  have bounds := (atoms_mem_iff tree _).mp endpoint.2
  have same := view.matching _ bounds.1 bounds.2 block member
  have labels := actual_event_source_labels run (atoms_nodup tree) (initial ∘ record) i
  simp only [positive, blockPositive, Finset.mem_filter, Finset.mem_univ, true_and,
    labelsAt_succ, linkLabels, Function.update_self, labels.2, same, newLabel, Function.comp_apply]

theorem boundary_eq {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : Frozen) (member : block ∈ state.shrinking) :
    boundary rank initial record (schedule owner tree) block =
      blockBoundaryNondrops (rank ∘ record) (initial ∘ record) (schedule owner tree) view.partition.block block.id := by
  ext i
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have endpoint := run.event_members _ (List.get_mem _ i)
  have firstBounds := (atoms_mem_iff tree _).mp endpoint.1
  have secondBounds := (atoms_mem_iff tree _).mp endpoint.2
  have first := view.matching _ firstBounds.1 firstBounds.2 block member
  have second := view.matching _ secondBounds.1 secondBounds.2 block member
  have labels := actual_event_source_labels run (atoms_nodup tree) (initial ∘ record) i
  simp only [boundary, blockBoundaryNondrops, Finset.mem_filter, Finset.mem_univ, true_and,
    labelsAt_succ, linkLabels, Function.update_self, labels.2, ne_eq, first, second, newLabel, Function.comp_apply]

theorem positive_count {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : Frozen) (member : block ∈ state.shrinking) :
    (positive rank initial record (schedule owner tree) block).card ≤ 3 := by
  rw [positive_eq view owner projection localOwners block member]
  obtain ⟨geometry⟩ := view.positive_geometry owner projection localOwners block.id
  exact geometry.bound

theorem boundary_count {lo hi : ℕ} {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi) (block : Frozen) (member : block ∈ state.shrinking)
    (H : ℕ) (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank (record key) ≤ H) :
    (boundary rank initial record (schedule owner tree) block).card ≤ 2*contractedGap H+3 := by
  rw [boundary_eq view owner projection localOwners block member]
  obtain ⟨geometry⟩ := view.boundary_geometry owner projection localOwners block.id H ranks
  exact geometry.bound (by unfold contractedGap; omega)

end Greedy.DepartureCells
