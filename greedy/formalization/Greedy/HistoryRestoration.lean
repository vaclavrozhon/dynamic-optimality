import Greedy.HistoryState
import Greedy.SnapshotPaid

/-!
The label history of the literal sequential restoration program. A port
reads at its original time and its label batch is stamped at that time,
after the read. Root ports merely contribute a zero change batch.
-/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

noncomputable def restorationHistory {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock : ℕ) :
    List (External n) → ℕ → ℕ → States n → LabelHistory.History (External n) → LabelHistory.History (External n)
  | [], _, _, _, history => history
  | record :: rest, stage, start, states, history =>
      let names := portNames (Splay.Rank.Snapshot.ofTree comparator) tree record start states
      let next := (restorePort (Splay.Rank.Snapshot.ofTree comparator) tree names
        (Execution.entryReader comparator K clock stage states record) record states).1
      restorationHistory comparator tree K clock rest (stage+1)
        (restoreNext (Splay.Rank.Snapshot.ofTree comparator) tree record start states) next
        (LabelHistory.update history (clock+1+stage) (RestorationJournal.labels comparator K next))

theorem restoration_one {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock stage : ℕ)
    (names : PaidNames) (record : External n) (states : States n)
    (history : LabelHistory.History (External n))
    (sound : Sound comparator K (clock+1+stage) states history)
    (chronology : Chronology (clock+1+stage) states) :
    let next := (restorePort (Splay.Rank.Snapshot.ofTree comparator) tree names
      (Execution.entryReader comparator K clock stage states record) record states).1
    Sound comparator K (clock+1+stage+1) next
      (LabelHistory.update history (clock+1+stage) (RestorationJournal.labels comparator K next)) ∧
      Chronology (clock+1+stage+1) next := by
  have preserved := restorePort_snapshots (Splay.Rank.Snapshot.ofTree comparator) tree names
    (Execution.entryReader comparator K clock stage states record) record states sound.snapshots
    (fun owner => reader_snapshot comparator K history (clock+1+stage) states sound.before sound.current record owner)
  have temporal := restorePort_chronology (Splay.Rank.Snapshot.ofTree comparator) tree names
    (Execution.entryReader comparator K clock stage states record) record (clock+1+stage) states chronology
    (fun _ => rfl)
  exact ⟨sound.update preserved ((chronology_iff ..).mp temporal).2, temporal⟩

theorem restoration_sound {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock : ℕ)
    (ports : List (External n)) (stage start : ℕ) (states : States n)
    (history : LabelHistory.History (External n))
    (sound : Sound comparator K (clock+1+stage) states history)
    (chronology : Chronology (clock+1+stage) states) :
    let result := freshRestorePorts (Splay.Rank.Snapshot.ofTree comparator) tree
      (Execution.entryReader comparator K clock) ports stage start states
    Sound comparator K (clock+1+stage+ports.length) result.states
      (restorationHistory comparator tree K clock ports stage start states history) ∧
      Chronology (clock+1+stage+ports.length) result.states := by
  induction ports generalizing stage start states history with
  | nil => simpa only [freshRestorePorts, restorationHistory, List.length_nil, Nat.add_zero] using And.intro sound chronology
  | cons record rest ih =>
      have first := restoration_one comparator tree K clock stage
        (portNames (Splay.Rank.Snapshot.ofTree comparator) tree record start states) record states history sound chronology
      have tail := ih (stage+1) (restoreNext (Splay.Rank.Snapshot.ofTree comparator) tree record start states) _ _
        (by simpa only [Nat.add_assoc] using first.1)
        (by simpa only [Nat.add_assoc] using first.2)
      simpa only [freshRestorePorts, restorationHistory, List.length_cons,
        Nat.add_assoc, Nat.add_comm 1] using tail

end Greedy.LabelSnapshots
