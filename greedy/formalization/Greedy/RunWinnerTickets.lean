import Greedy.WinnerFamily

/-! An actual membership wins internally at most four times in the whole run. -/

namespace Greedy.WinnerTickets

open Splay.Tree Splay.Tree.BST Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.HeapAllocation
open ClosedFamilies

noncomputable def total {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)} :
    Execution.Run K first last requests → ℕ → ℕ → ℕ
  | .done _, _, _ => 0
  | .rotate _ _ _ rest, family, joined => total rest family joined
  | .access (first := first) request _ _ data _ rest, family, joined =>
      familyWins data (RunJournal.prepared first request) (Execution.source request) family joined + total rest family joined

theorem isolated_total_zero {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (inv : FamilyOrder.Invariant first.clock first.next first.blocks) (family joined : ℕ)
    (isolated : AllSourcesClosed (family := family) (Isolated joined) execution) : total execution family joined = 0 := by
  induction execution with
  | done => rfl
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      exact ih afterValid (FamilyOrder.complete_rotation_invariant first after rotation K data inv) isolated.2
  | @access first last requests request root decomposition data afterValid rest ih =>
      have prepared := FamilyOrder.convertHeap_invariant first.comparator.externalDepth
        (fun owner _ => decide (owner = Execution.source request)) first.next first.blocks inv
      have head := isolated_family_zero data (RunJournal.prepared first request) (Execution.source request) family joined
        ((CreatorPhase.prepared_ready first request valid).valid _) prepared isolated.2.1
      have tail := ih afterValid (FamilyOrder.afterAccess_invariant first request K decomposition data inv afterValid) isolated.2.2
      simp only [total, head, tail, zero_add]

theorem total_le_four {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (inv : FamilyOrder.Invariant first.clock first.next first.blocks) (family joined : ℕ) : total execution family joined ≤ 4 := by
  induction execution with
  | done => simp [total]
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      exact ih afterValid (FamilyOrder.complete_rotation_invariant first after rotation K data inv)
  | @access first last requests request root decomposition data afterValid rest ih =>
      have nextInv := FamilyOrder.afterAccess_invariant first request K decomposition data inv afterValid
      by_cases zero : familyWins data (RunJournal.prepared first request) (Execution.source request) family joined = 0
      · simpa only [total, zero, zero_add] using ih afterValid nextInv
      · obtain ⟨side, block, member, named, contributes⟩ :=
          nonzero_piece data (RunJournal.prepared first request) (Execution.source request) family joined zero
        have ready := CreatorPhase.prepared_ready first request valid
        have present := part_nonzero_contains data (RunJournal.prepared first request) (Execution.source request) side block joined
          (ready.valid _ side) member contributes
        have remaining := remaining_sources_isolated first request K root decomposition data inv afterValid rest side block member present
        rw [named] at remaining
        have tailZero := isolated_total_zero rest afterValid nextInv family joined remaining
        have prepared := FamilyOrder.convertHeap_invariant first.comparator.externalDepth
          (fun owner _ => decide (owner = Execution.source request)) first.next first.blocks inv
        simpa only [total, tailZero, Nat.add_zero] using
          family_bound data (RunJournal.prepared first request) (Execution.source request) family joined (ready.valid _) prepared

theorem initialized_total_le_four {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests) (family joined : ℕ) :
    total execution family joined ≤ 4 :=
  total_le_four execution (Execution.initial_valid initial comparator K)
    (FamilyOrder.initial_invariant (Snapshot.ofTree comparator) _ K) family joined

end Greedy.WinnerTickets
