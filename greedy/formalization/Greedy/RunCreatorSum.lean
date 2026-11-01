import Greedy.FamilyPhaseSum

/-!
The signed coefficient of a family across the actual complete execution
is at most three. Its first nonzero access closes the historical cut;
all later accesses have zero coefficient, including after rotations.
-/

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Tree.BST Splay.Rank
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.FrozenHistory ClosedFamilies

noncomputable def total {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)} :
    Execution.Run K first last requests → ℕ → ℕ → ℕ → ℤ
  | .done _, _, _, _ => 0
  | .rotate _ _ _ rest, creator, family, time => total rest creator family time
  | .access (first := first) request _ _ data _ rest, creator, family, time =>
      familyCoefficient data (RunJournal.prepared first request) (Execution.source request) creator family time +
        total rest creator family time

theorem closed_phase_zero {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : GreedyMerge.PathPlateau.Decomposition oldTree access}
    (data : GreedyMerge.ActualLinks.AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (creator family time : ℕ)
    (valid : ∀ side, Valid source.val side (states source side))
    (closed : HeapClosed family (AvoidsCut (time+1)) states) :
    familyCoefficient data states source creator family time = 0 := by
  by_contra nonzero
  obtain ⟨side, block, member, _created, named, contributes⟩ := nonzero_piece data states source creator family time nonzero
  have avoids := closed.frozen (encode n (source, side)) block (by simpa [table] using member) named
  exact avoids (part_nonzero_crosses data states source side block time (valid side) member contributes)

theorem all_closed_total_zero {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid) (creator family time : ℕ)
    (closed : AllSourcesClosed (family := family) (AvoidsCut (time+1)) execution) : total execution creator family time = 0 := by
  induction execution with
  | done => rfl
  | @rotate first last after depth requests rotation data afterValid rest ih => exact ih afterValid closed.2
  | @access first last requests request root decomposition data afterValid rest ih =>
      have head := closed_phase_zero data (RunJournal.prepared first request) (Execution.source request) creator family time
        ((prepared_ready first request valid).valid _) closed.2.1
      simp only [total, head, ih afterValid closed.2.2, add_zero]

theorem total_abs_le_three {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (inv : FamilyOrder.Invariant first.clock first.next first.blocks) (creator family time : ℕ) :
    |total execution creator family time| ≤ 3 := by
  induction execution with
  | done => simp [total]
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      exact ih afterValid (FamilyOrder.complete_rotation_invariant first after rotation K data inv)
  | @access first last requests request root decomposition data afterValid rest ih =>
      by_cases zero : familyCoefficient data (RunJournal.prepared first request) (Execution.source request) creator family time = 0
      · simpa only [total, zero, zero_add] using
          ih afterValid (FamilyOrder.afterAccess_invariant first request K decomposition data inv afterValid)
      · obtain ⟨side, block, member, _created, named, contributes⟩ :=
          nonzero_piece data (RunJournal.prepared first request) (Execution.source request) creator family time zero
        have crosses := part_nonzero_crosses data (RunJournal.prepared first request) (Execution.source request) side block time
          ((prepared_ready first request valid).valid _ side) member contributes
        have remaining := remaining_sources_avoid first request K root decomposition data inv afterValid rest side block member crosses
        rw [named] at remaining
        have tailZero := all_closed_total_zero rest afterValid creator family time remaining
        simpa only [total, tailZero, add_zero] using prepared_family_bound first request K decomposition data valid root inv creator family time

theorem initialized_total_abs_le_three {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests) (creator family time : ℕ) :
    |total execution creator family time| ≤ 3 :=
  total_abs_le_three execution (Execution.initial_valid initial comparator K)
    (FamilyOrder.initial_invariant (Snapshot.ofTree comparator) _ K) creator family time

end Greedy.CreatorPhase
