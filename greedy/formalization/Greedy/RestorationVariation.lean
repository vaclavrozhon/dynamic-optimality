import Greedy.JournalAbsoluteVariation
import Greedy.HistoryRestoration

/-! The actual restoration history and journal have identical variation. -/

namespace Greedy.RestorationJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open EntryJournal

theorem one_labels {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator K states) :
    (run state (one comparator tree K names makeEntry record states)).label =
      labels comparator K (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1 := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simpa only [one, parent, restorePort, run] using agree
  | some owner => simp only [one, parent, run, run_batch]

theorem one_history_variation {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (time : ℕ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (history : LabelHistory.History (External n))
    (agree : state.label = labels comparator K states) (current : LabelHistory.current history = state.label) :
    LabelHistory.variation (LabelHistory.update history time
      (labels comparator K (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1)) =
        LabelHistory.variation history + total absoluteChange state (one comparator tree K names makeEntry record states) := by
  rw [LabelHistory.variation_update, current]
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simp [one, parent, restorePort, total, agree]
  | some owner => simp only [one, parent, total, absoluteChange, zero_add, batch_absolute,
      step, EntryJournal.encode, WeightedMemory.step]

theorem restoration_agrees {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock : ℕ)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (history : LabelHistory.History (External n))
    (agree : state.label = labels comparator K states) (current : LabelHistory.current history = state.label) :
    let actions := program comparator tree K (Execution.entryReader comparator K clock) ports stage start states
    let finalHistory := LabelSnapshots.restorationHistory comparator tree K clock ports stage start states history
    let after := freshRestorePorts (Snapshot.ofTree comparator) tree (Execution.entryReader comparator K clock) ports stage start states
    (run state actions).label = labels comparator K after.states ∧
      LabelHistory.current finalHistory = (run state actions).label ∧
      LabelHistory.variation finalHistory = LabelHistory.variation history + total absoluteChange state actions := by
  induction ports generalizing stage start states state history with
  | nil => exact ⟨agree, current, by simp [LabelSnapshots.restorationHistory, program, total]⟩
  | cons record rest ih =>
      let names := portNames (Snapshot.ofTree comparator) tree record start states
      let makeEntry := Execution.entryReader comparator K clock stage states record
      let next := (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1
      let head := one comparator tree K names makeEntry record states
      let nextHistory := LabelHistory.update history (clock+1+stage) (labels comparator K next)
      have headLabels := one_labels comparator tree K names makeEntry record states state agree
      have headCurrent : LabelHistory.current nextHistory = (run state head).label :=
        (LabelHistory.current_update ..).trans headLabels.symm
      have headVariation := one_history_variation comparator tree K (clock+1+stage) names makeEntry record states state history agree current
      have tail := ih (stage+1) (restoreNext (Snapshot.ofTree comparator) tree record start states) next
        (run state head) nextHistory headLabels headCurrent
      dsimp only
      simp only [program, LabelSnapshots.restorationHistory, run_append, total_append]
      refine ⟨tail.1, tail.2.1, ?_⟩
      change LabelHistory.variation
        (LabelSnapshots.restorationHistory comparator tree K clock rest (stage+1)
          (restoreNext (Snapshot.ofTree comparator) tree record start states) next nextHistory) = _
      rw [tail.2.2]
      change LabelHistory.variation nextHistory + _ = _
      rw [show LabelHistory.variation nextHistory = LabelHistory.variation history + total absoluteChange state head from headVariation]
      exact add_assoc _ _ _

theorem administration_agrees {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock : ℕ)
    (ports : List (External n)) (stage start : ℕ) (prepared : HeapSides n)
    (state : WeightedMemory.State (External n)) (history : LabelHistory.History (External n))
    (current : LabelHistory.current history = state.label) :
    let actions := administration comparator tree K (Execution.entryReader comparator K clock) ports stage start prepared
    let finalHistory := LabelSnapshots.restorationHistory comparator tree K clock ports stage start prepared
      (LabelHistory.update history clock (labels comparator K prepared))
    let after := freshRestorePorts (Snapshot.ofTree comparator) tree (Execution.entryReader comparator K clock) ports stage start prepared
    (run state actions).label = labels comparator K after.states ∧
      LabelHistory.current finalHistory = (run state actions).label ∧
      LabelHistory.variation finalHistory = LabelHistory.variation history + total absoluteChange state actions := by
  let target := labels comparator K prepared
  have batchLabels : (run state (batch target)).label = target := by simp
  have batchCurrent : LabelHistory.current (LabelHistory.update history clock target) = (run state (batch target)).label := by simp
  have tail := restoration_agrees comparator tree K clock ports stage start prepared
    (run state (batch target)) (LabelHistory.update history clock target) batchLabels batchCurrent
  dsimp only
  simp only [administration, run_append, total_append]
  refine ⟨tail.1, tail.2.1, ?_⟩
  rw [tail.2.2, LabelHistory.update_batch_variation history clock state target current]
  exact add_assoc _ _ _

end Greedy.RestorationJournal
