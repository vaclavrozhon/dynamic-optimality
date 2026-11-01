import Greedy.DepartureCells

/-! Local weighted budgets for increases and boundary links without a drop. -/

namespace Greedy.DepartureAmounts

open Splay.Tree Splay.Analysis GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule GreedyMerge.AccessSourceAccounting
open GreedyForest.Phase
open scoped BigOperators

inductive Metric where
  | increase | boundary

noncomputable def cells (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (block : Frozen) : Finset (Fin events.length) :=
  match metric with
  | .increase => DepartureCells.positive rank initial record events block
  | .boundary => DepartureCells.boundary rank initial record events block

def weight (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ) : ℤ :=
  match metric with
  | .increase => max 0 (DepartureCells.newLabel rank record edge - initial (record edge.2))
  | .boundary => 1

def range (metric : Metric) (H : ℕ) : ℤ :=
  match metric with
  | .increase => (contractedGap H : ℤ)-1
  | .boundary => 1

def allowance (metric : Metric) (H : ℕ) : ℤ :=
  match metric with
  | .increase => 3*((contractedGap H : ℤ)-1)
  | .boundary => 2*(contractedGap H : ℤ)+3

noncomputable def amount {lo hi : ℕ} (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record owner : ℕ → ℕ) (tree : BST lo hi) (block : Frozen) : ℤ :=
  ∑ i ∈ cells metric rank initial record (schedule owner tree) block,
    weight metric rank initial record ((schedule owner tree).get i)

theorem range_nonneg (metric : Metric) (H : ℕ) : 0 ≤ range metric H := by
  cases metric <;> simp only [range, contractedGap] <;> omega

theorem allowance_nonneg (metric : Metric) (H : ℕ) : 0 ≤ allowance metric H := by
  cases metric <;> simp only [allowance, contractedGap] <;> omega

theorem cell_loser (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (events : List (ℕ × ℕ)) (block : Frozen) (i : Fin events.length) (member : i ∈ cells metric rank initial record events block) :
    record (events.get i).2 ∈ ClosedInstances.keys block := by
  cases metric
  · exact DepartureCells.positive_loser rank initial record events block i member
  · exact DepartureCells.boundary_loser rank initial record events block i member

theorem weight_nonneg (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ) (edge : ℕ × ℕ) :
    0 ≤ weight metric rank initial record edge := by
  cases metric
  · exact le_max_left _ _
  · exact zero_le_one

theorem weight_bound (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ) (record : ℕ → ℕ)
    (edge : ℕ × ℕ) (H : ℕ) (height : rank (record edge.2) ≤ H) (lower : 1 ≤ initial (record edge.2)) :
    weight metric rank initial record edge ≤ range metric H := by
  cases metric with
  | boundary => exact le_refl _
  | increase =>
      have upper : DepartureCells.newLabel rank record edge ≤ (contractedGap H : ℤ) := by
        change (contractedGap (rank (record edge.2) - rank (record edge.1)) : ℤ) ≤ _
        exact_mod_cast contractedGap_mono ((Nat.sub_le (rank (record edge.2)) (rank (record edge.1))).trans height)
      have nonneg := range_nonneg Metric.increase H
      change 0 ≤ (contractedGap H : ℤ)-1 at nonneg
      change max 0 (_ - _) ≤ (contractedGap H : ℤ)-1
      omega

theorem spec {lo hi : ℕ} (metric : Metric) {rank : ℕ → ℕ} {initial : ℕ → ℤ} {record : ℕ → ℕ}
    {tree : BST lo hi} {state : SideState} (view : SideView rank initial record tree state)
    (owner : ℕ → ℕ) (projection : Projection (rank ∘ record) owner tree)
    (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (injective : Set.InjOn record {key | key ∈ atoms tree})
    (block : Frozen) (member : block ∈ state.shrinking) (H : ℕ)
    (ranks : ∀ key, 2*lo ≤ key → key ≤ 2*hi → rank (record key) ≤ H) :
    0 ≤ amount metric rank initial record owner tree block ∧
      amount metric rank initial record owner tree block ≤ allowance metric H ∧
      (ClosedInstances.Small block → amount metric rank initial record owner tree block ≤ range metric H) ∧
      (amount metric rank initial record owner tree block ≠ 0 →
        ∃ edge ∈ schedule owner tree, record edge.2 ∈ ClosedInstances.keys block) := by
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have each : ∀ i ∈ cells metric rank initial record (schedule owner tree) block,
      weight metric rank initial record ((schedule owner tree).get i) ≤ range metric H := by
    intro i _
    have atom := (run.event_members _ (List.get_mem _ i)).2
    have bounds := (atoms_mem_iff tree _).mp atom
    exact weight_bound metric rank initial record _ H (ranks _ bounds.1 bounds.2)
      (IncomingExcess.view_label_bounds view H ranks _ atom).1
  refine ⟨Finset.sum_nonneg (fun _ _ => weight_nonneg metric _ _ _ _), ?_, ?_, ?_⟩
  · cases metric with
    | increase =>
        exact AtomicDepartures.sum_le_capacity _ _ _ 3 (range_nonneg .increase H)
          (DepartureCells.positive_count view owner projection localOwners block member) each
    | boundary =>
        have bound := AtomicDepartures.sum_le_capacity _ _ _ (2*contractedGap H+3) (range_nonneg .boundary H)
          (DepartureCells.boundary_count view owner projection localOwners block member H ranks) each
        simpa only [amount, cells, range, allowance, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_one] using bound
  · intro small
    have bound := AtomicDepartures.sum_le_capacity _ _ _ 1 (range_nonneg _ H)
      (AtomicDepartures.small_count rank record owner tree projection localOwners injective block small _
        (cell_loser metric rank initial record _ block)) each
    simpa only [amount, Nat.cast_one, one_mul] using bound
  · intro nonzero
    obtain ⟨i, iMem, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
    exact ⟨_, List.get_mem _ i, cell_loser metric rank initial record _ block i iMem⟩

end Greedy.DepartureAmounts
