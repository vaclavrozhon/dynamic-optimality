import Greedy.HistoryAdministration
import Greedy.HistoryAccess

/-!
Future changes are appended with their actual timestamps. This preserves
historical labels of retired entries as well as entries still in the heap.
-/

namespace Greedy.LabelHistory

variable {Record : Type*}

def Future (before after : History Record) (clock : ℕ) : Prop :=
  ∃ tail : List (Change Record), after = ⟨before.initial, before.changes ++ tail⟩ ∧
    ∀ change ∈ tail, clock ≤ change.time

theorem Future.refl (history : History Record) (clock : ℕ) : Future history history clock :=
  ⟨[], by cases history; simp, by simp⟩

theorem Future.weaken {before after : History Record} {clock : ℕ}
    (extension : Future before after clock) (earlier : ℕ) (bound : earlier ≤ clock) : Future before after earlier := by
  obtain ⟨tail, equal, times⟩ := extension
  exact ⟨tail, equal, fun change member => bound.trans (times change member)⟩

theorem Future.trans {first middle last : History Record} {clock : ℕ}
    (head : Future first middle clock) (tail : Future middle last clock) : Future first last clock := by
  obtain ⟨firstTail, firstEq, firstTimes⟩ := head
  obtain ⟨lastTail, lastEq, lastTimes⟩ := tail
  refine ⟨firstTail ++ lastTail, ?_, ?_⟩
  · rw [lastEq, firstEq]
    simp [List.append_assoc]
  · intro change member
    rcases List.mem_append.mp member with firstMem | lastMem
    · exact firstTimes change firstMem
    · exact lastTimes change lastMem

theorem future_update (history : History Record) (clock : ℕ) (target : Record → ℤ) :
    Future history (update history clock target) clock :=
  ⟨[⟨clock, fun record => target record - current history record⟩], rfl,
    by intro change member; have same := List.mem_singleton.mp member; subst change; exact le_refl _⟩

theorem Future.past {before after : History Record} {clock : ℕ} (extension : Future before after clock)
    (time : ℕ) (bound : time ≤ clock) : value after time = value before time := by
  obtain ⟨tail, rfl, times⟩ := extension
  funext record
  have zero : (tail.map (fun change => if change.time < time then change.delta record else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro value member
    obtain ⟨change, changeMem, rfl⟩ := List.mem_map.mp member
    simp [show ¬change.time < time by have := times change changeMem; omega]
  simp [value, zero]

end Greedy.LabelHistory

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter

theorem HeapSnapshots.future {n clock : ℕ} {history finalHistory : LabelHistory.History (External n)}
    {states : States n} (snapshots : HeapSnapshots history states)
    (extension : LabelHistory.Future history finalHistory clock) (before : BeforeTime (clock+1) states) :
    HeapSnapshots finalHistory states := by
  intro owner side entry creator member
  have past : entry.joined ≤ clock := by have := before owner side entry (tagged_entry _ _ _ member); omega
  have equal (key : ℕ) : atKey finalHistory entry.joined key = atKey history entry.joined key := by
    unfold atKey
    split_ifs
    · exact congrFun (extension.past entry.joined past) _
    · rfl
  simpa only [Snapshot, equal] using snapshots owner side entry creator member

theorem restoration_future {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock : ℕ)
    (ports : List (External n)) (stage start : ℕ) (states : States n) (history : LabelHistory.History (External n)) :
    LabelHistory.Future history (restorationHistory comparator tree K clock ports stage start states history) (clock+1+stage) := by
  induction ports generalizing stage start states history with
  | nil => exact .refl _ _
  | cons record rest ih =>
      apply (LabelHistory.future_update history (clock+1+stage) _).trans
      exact (ih (stage+1) _ _ _).weaken (clock+1+stage) (by omega)

theorem access_future {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (clock : ℕ) (states : States n) (events : List (External n × External n)) (history : LabelHistory.History (External n)) :
    LabelHistory.Future history (accessHistory comparator K source sourceSide clock states events history) clock := by
  induction events generalizing clock states history with
  | nil => exact .refl _ _
  | cons event rest ih =>
      apply (LabelHistory.future_update history clock _).trans
      exact (ih (clock+1) _ _).weaken clock (by omega)

theorem plan_future {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n)
    (history : LabelHistory.History (External n)) :
    LabelHistory.Future history (planHistory profile tree plan K clock start states history) clock := by
  apply (LabelHistory.future_update history clock _).trans
  exact (restoration_future after tree K clock _ 0 _ _ _).weaken clock (by omega)

theorem refinement_future {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (clock start : ℕ) (states : States n) (history : LabelHistory.History (External n)) :
    LabelHistory.Future history (refinementHistory comparator tree K ports clock start states history) clock := by
  apply (LabelHistory.future_update history clock _).trans
  exact (restoration_future comparator tree K clock ports 0 _ _ _).weaken clock (by omega)

end Greedy.LabelSnapshots
