import Greedy.PhaseShiftTelescope
import Greedy.RunCreatorWindows

/-! The actual stored creator-shift sum is bounded by six times variation. -/

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Tree.BST Splay.Rank GreedyMerge.OrderedBlocks
open scoped BigOperators

noncomputable def families {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)} :
    Execution.Run K first last requests → Finset ℕ
  | .done _ => ∅
  | .rotate _ _ _ rest => families rest
  | .access (first := first) request _ _ _ _ rest =>
      ((pieces (RunJournal.prepared first request) (Execution.source request)).image (fun piece => piece.2.family)) ∪ families rest

noncomputable def shiftTotal {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)} :
    Execution.Run K first last requests → ℤ
  | .done _ => 0
  | .rotate _ _ _ rest => shiftTotal rest
  | .access (first := first) request _ _ data _ rest =>
      shiftPhase data (RunJournal.prepared first request) (Execution.source request) + shiftTotal rest

theorem shiftTotal_telescope {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (history : LabelHistory.History (External n)) (snapshots : LabelSnapshots.AllSourcesSnapshots history execution)
    (names : Finset ℕ) (covers : families execution ⊆ names) :
    shiftTotal execution = LabelHistory.pairing history (fun creator time => ∑ family ∈ names, total execution creator.val family time) := by
  classical
  induction execution with
  | done => simp [shiftTotal, total, LabelHistory.pairing_zero]
  | @rotate first last after depth requests rotation data afterValid rest ih => exact ih afterValid snapshots.2 covers
  | @access first last requests request root decomposition data afterValid rest ih =>
      have phaseNames : ∀ side block, block ∈ (RunJournal.prepared first request (Execution.source request) side).shrinking → block.family ∈ names := by
        intro side block member
        exact covers (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(side, block), (mem_pieces ..).mpr member, rfl⟩))
      have head := shiftPhase_telescope data history (RunJournal.prepared first request) (Execution.source request)
        ((prepared_ready first request valid).valid _) snapshots.2.1 names phaseNames
      have tail := ih afterValid snapshots.2.2 (fun family member => covers (Finset.mem_union_right _ member))
      change shiftPhase data (RunJournal.prepared first request) (Execution.source request) + shiftTotal rest = _
      rw [head, tail, ← LabelHistory.pairing_add]
      congr 1
      funext creator time
      simp only [total, Finset.sum_add_distrib]

theorem initialized_shift_bound {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests)
    (history : LabelHistory.History (External n)) (snapshots : LabelSnapshots.AllSourcesSnapshots history execution) :
    shiftTotal execution ≤ 6 * LabelHistory.variation history := by
  rw [shiftTotal_telescope execution (Execution.initial_valid initial comparator K) history snapshots (families execution) (Finset.Subset.refl _)]
  exact LabelHistory.pairing_bound history _ 6
    (fun record time => initialized_summed_coefficient_bound initial comparator K execution (families execution) record time)

theorem exists_bounded_shift_history {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests) :
    ∃ history, LabelSnapshots.Sound last.comparator K last.clock last.blocks history ∧
      LabelSnapshots.AllSourcesSnapshots history execution ∧ shiftTotal execution ≤ 6 * LabelHistory.variation history := by
  obtain ⟨history, sound, snapshots⟩ := LabelSnapshots.initialized_all_snapshots initial comparator K execution
  exact ⟨history, sound, snapshots, initialized_shift_bound initial comparator K execution history snapshots⟩

end Greedy.CreatorPhase
