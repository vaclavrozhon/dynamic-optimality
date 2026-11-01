import Greedy.InstanceCharge
import Greedy.RunBirthJournal

/-! Sum lifetime charges over the actual finite instance registry. -/

namespace Greedy.InstanceCharge

open Splay.Tree Splay.Tree.BST Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open scoped BigOperators

theorem sum_phase_eq {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (charge : Charge n)
    (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (names : Finset ℕ) (covered : RunBirthJournal.Covered names states) :
    (∑ id ∈ names, phase charge data states source id) =
      ∑ piece ∈ CreatorPhase.pieces states source, charge data states source piece.1 piece.2 := by
  classical
  unfold phase
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro piece member
  have present : piece.2.id ∈ names := covered piece.2.id ⟨source, piece.1,
    List.mem_append_left _ (List.mem_map.mpr ⟨piece.2, (CreatorPhase.mem_pieces ..).mp member, rfl⟩)⟩
  rw [Finset.sum_eq_single piece.2.id]
  · simp only [if_true]
  · intro id _ different
    exact if_neg (Ne.symm different)
  · exact fun absent => False.elim (absent present)

noncomputable def mass {n : ℕ} (charge : Charge n) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} : Execution.Run K first last requests → ℤ
  | .done _ => 0
  | .rotate _ _ _ rest => mass charge rest
  | .access (first := first) request _ _ data _ rest =>
      (∑ piece ∈ CreatorPhase.pieces (RunJournal.prepared first request) (Execution.source request),
        charge data (RunJournal.prepared first request) (Execution.source request) piece.1 piece.2) + mass charge rest

theorem sum_total_eq {n : ℕ} (charge : Charge n) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} (execution : Execution.Run K first last requests)
    (names : Finset ℕ) (covered : RunBirthJournal.AllSourcesCovered names execution) :
    (∑ id ∈ names, total charge execution id) = mass charge execution := by
  induction execution with
  | done => simp only [total, mass, Finset.sum_const_zero]
  | rotate _ _ _ rest ih => exact ih covered.2
  | access request root decomposition data afterValid rest ih =>
      simp only [total, mass, Finset.sum_add_distrib, ih covered.2.2,
        sum_phase_eq charge data _ _ names covered.2.1]

theorem mass_bound {n : ℕ} (charge : Charge n) (range allowance : ℤ)
    (rangeNonneg : 0 ≤ range) (allowanceNonneg : 0 ≤ allowance) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} (execution : Execution.Run K first last requests)
    (valid : first.Valid) (bounded : Bounded charge range allowance execution) :
    mass charge execution ≤ (allowance + range) * (first.next + execution.births : ℕ) := by
  rw [← sum_total_eq charge execution (RunBirthJournal.registry execution) (RunBirthJournal.registry_covers execution valid)]
  calc
    _ ≤ ∑ _id ∈ RunBirthJournal.registry execution, (allowance + range) :=
      Finset.sum_le_sum (fun id _ => lifetime_bound charge range allowance rangeNonneg allowanceNonneg execution valid bounded id)
    _ = (allowance + range) * ((RunBirthJournal.registry execution).card : ℤ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast RunBirthJournal.registry_card execution)
      (add_nonneg allowanceNonneg rangeNonneg)

theorem initialized_mass_bound {n : ℕ} (charge : Charge n) (range allowance : ℤ)
    (rangeNonneg : 0 ≤ range) (allowanceNonneg : 0 ≤ allowance)
    (initial comparator : BST 0 n) (K : ℤ) {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests)
    (bounded : Bounded charge range allowance execution) :
    mass charge execution ≤ (allowance + range) * (2*(2*n+1) + execution.births : ℕ) :=
  mass_bound charge range allowance rangeNonneg allowanceNonneg execution (Execution.initial_valid initial comparator K) bounded

end Greedy.InstanceCharge
