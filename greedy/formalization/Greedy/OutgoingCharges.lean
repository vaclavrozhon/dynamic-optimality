import Greedy.OutgoingExcess

/-!
Every positive excess is assigned either to its nonroot winner's source
instance or, when its winner is the final root, to its loser's instance.
Each chosen instance has an actual departing record in that phase.
-/

namespace Greedy.OutgoingExcess

open Splay.Tree Splay.Analysis GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.ActualBlockPartition GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.AccessSourceAccounting GreedyForest.Phase
open scoped BigOperators

inductive Metric where
  | nonrootWinner | rootLoser

def Selected (metric : Metric) (root : ℕ) (record : ℕ → ℕ) (block : Frozen) (edge : ℕ × ℕ) : Prop :=
  match metric with
  | .nonrootWinner => record edge.1 ∈ blockKeys block ∧ record edge.2 ∉ blockKeys block ∧ edge.1 ≠ root
  | .rootLoser => record edge.2 ∈ blockKeys block ∧ record edge.1 ∉ blockKeys block ∧ edge.1 = root

noncomputable def weight (metric : Metric) (root : ℕ) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record : ℕ → ℕ) (block : Frozen) (edge : ℕ × ℕ) : ℤ := by
  classical
  exact if Selected metric root record block edge then extra rank initial record edge else 0

noncomputable def amount {lo hi : ℕ} (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record owner : ℕ → ℕ) (tree : BST lo hi) (block : Frozen) : ℤ :=
  ∑ edge ∈ (schedule owner tree).toFinset, weight metric (treeOwner owner tree) rank initial record block edge

def range (metric : Metric) (H : ℕ) : ℤ :=
  match metric with
  | .nonrootWinner => 4*((contractedGap H : ℤ)-1)
  | .rootLoser => (contractedGap H : ℤ)-1

theorem range_nonneg (metric : Metric) (H : ℕ) : 0 ≤ range metric H := by
  cases metric <;> simp only [range, contractedGap] <;> omega

theorem weight_nonneg (metric : Metric) (root : ℕ) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record : ℕ → ℕ) (block : Frozen) (edge : ℕ × ℕ) : 0 ≤ weight metric root rank initial record block edge := by
  unfold weight
  split_ifs
  · exact extra_nonneg _ _ _ _
  · exact le_rfl

theorem weight_selected (metric : Metric) (root : ℕ) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record : ℕ → ℕ) (block : Frozen) (edge : ℕ × ℕ)
    (nonzero : weight metric root rank initial record block edge ≠ 0) : Selected metric root record block edge := by
  unfold weight at nonzero
  split_ifs at nonzero with selected
  · exact selected
  · exact False.elim (nonzero rfl)

theorem winner_capacity {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection rank owner tree) (localOwners : LocalOwners rank owner lo hi)
    (events : Finset (ℕ × ℕ)) (subset : events ⊆ (schedule owner tree).toFinset)
    (winner : ℕ) (fixed : ∀ edge ∈ events, edge.1 = winner) : events.card ≤ 4 := by
  have included : events ⊆ (schedule owner tree).toFinset.filter (fun edge => edge.1 = winner) :=
    fun edge member => Finset.mem_filter.mpr ⟨subset member, fixed edge member⟩
  calc
    _ ≤ ((schedule owner tree).toFinset.filter (fun edge => edge.1 = winner)).card := Finset.card_le_card included
    _ = ((schedule owner tree).filter (fun edge => edge.1 == winner)).toFinset.card := by simp only [List.toFinset_filter, beq_iff_eq]
    _ ≤ ((schedule owner tree).filter (fun edge => edge.1 == winner)).length := List.toFinset_card_le _
    _ ≤ 4 := by rw [← List.countP_eq_length_filter]; exact schedule_winner_count_le_four rank owner tree winner projection localOwners

theorem small_winner_capacity {lo hi : ℕ} (rank record owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection (rank ∘ record) owner tree) (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (injective : Set.InjOn record {key | key ∈ atoms tree}) (block : Frozen) (small : ClosedInstances.Small block)
    (events : Finset (ℕ × ℕ)) (subset : events ⊆ (schedule owner tree).toFinset)
    (winners : ∀ edge ∈ events, record edge.1 ∈ ClosedInstances.keys block) : events.card ≤ 4 := by
  by_cases nonempty : events.Nonempty
  · obtain ⟨first, firstMem⟩ := nonempty
    have run := schedule_run (rank ∘ record) owner tree projection localOwners
    apply winner_capacity (rank ∘ record) owner tree projection localOwners events subset first.1
    intro edge member
    apply injective (run.event_members _ (List.mem_toFinset.mp (subset member))).1
      (run.event_members _ (List.mem_toFinset.mp (subset firstMem))).1
    exact Finset.card_le_one.mp small _ (winners edge member) _ (winners first firstMem)
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty, Finset.card_empty]
    omega

theorem small_loser_capacity {lo hi : ℕ} (rank record owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection (rank ∘ record) owner tree) (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (injective : Set.InjOn record {key | key ∈ atoms tree}) (block : Frozen) (small : ClosedInstances.Small block)
    (events : Finset (ℕ × ℕ)) (subset : events ⊆ (schedule owner tree).toFinset)
    (losers : ∀ edge ∈ events, record edge.2 ∈ ClosedInstances.keys block) : events.card ≤ 1 := by
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  have unique := run_losers_nodup run (atoms_nodup tree)
  apply Finset.card_le_one.mpr
  intro first firstMem second secondMem
  have firstEvent := List.mem_toFinset.mp (subset firstMem)
  have secondEvent := List.mem_toFinset.mp (subset secondMem)
  apply List.inj_on_of_nodup_map unique firstEvent secondEvent
  apply injective (run.event_members _ firstEvent).2 (run.event_members _ secondEvent).2
  exact Finset.card_le_one.mp small _ (losers first firstMem) _ (losers second secondMem)

theorem amount_le_capacity {lo hi : ℕ} (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record owner : ℕ → ℕ) (tree : BST lo hi) (block : Frozen) (H capacity : ℕ)
    (bounded : ∀ edge ∈ schedule owner tree, extra rank initial record edge ≤ (contractedGap H : ℤ)-1)
    (size : ((schedule owner tree).toFinset.filter
      (fun edge => weight metric (treeOwner owner tree) rank initial record block edge ≠ 0)).card ≤ capacity) :
    amount metric rank initial record owner tree block ≤ (capacity : ℤ)*((contractedGap H : ℤ)-1) := by
  classical
  let support := (schedule owner tree).toFinset.filter
    (fun edge => weight metric (treeOwner owner tree) rank initial record block edge ≠ 0)
  have restricted : amount metric rank initial record owner tree block =
      ∑ edge ∈ support, weight metric (treeOwner owner tree) rank initial record block edge := by
    unfold amount support
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases zero : weight metric (treeOwner owner tree) rank initial record block edge = 0 <;> simp [zero]
  rw [restricted]
  apply AtomicDepartures.sum_le_capacity _ _ _ capacity (by unfold contractedGap; omega) size
  intro edge member
  have selected := weight_selected metric _ rank initial record block edge (Finset.mem_filter.mp member).2
  simp only [weight, if_pos selected]
  exact bounded edge (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)

theorem amount_departure {lo hi : ℕ} (metric : Metric) (rank : ℕ → ℕ) (initial : ℕ → ℤ)
    (record owner : ℕ → ℕ) (tree : BST lo hi)
    (projection : Projection (rank ∘ record) owner tree) (localOwners : LocalOwners (rank ∘ record) owner lo hi)
    (block : Frozen) (nonzero : amount metric rank initial record owner tree block ≠ 0) :
    ∃ event ∈ schedule owner tree, record event.2 ∈ ClosedInstances.keys block := by
  obtain ⟨edge, edgeMem, contributes⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  have selected := weight_selected metric _ rank initial record block edge contributes
  have run := schedule_run (rank ∘ record) owner tree projection localOwners
  cases metric with
  | rootLoser => exact ⟨edge, List.mem_toFinset.mp edgeMem, List.mem_toFinset.mpr selected.1⟩
  | nonrootWinner =>
      have winnerMem := (run.event_members edge (List.mem_toFinset.mp edgeMem)).1
      have departure : edge.1 ∈ (schedule owner tree).map Prod.snd := by
        by_contra absent
        have survivor := (GreedyMerge.HistoryProcess.run_survivor_iff run (atoms_nodup tree) edge.1).mpr ⟨winnerMem, absent⟩
        exact selected.2.2 (List.mem_singleton.mp survivor)
      obtain ⟨event, eventMem, same⟩ := List.mem_map.mp departure
      exact ⟨event, eventMem, List.mem_toFinset.mpr (by rw [same]; exact selected.1)⟩

end Greedy.OutgoingExcess
