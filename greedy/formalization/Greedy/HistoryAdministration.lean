import Greedy.HistoryRestoration
import Greedy.SnapshotStructural
import Greedy.AdministrationJournal

/-! Exact sparse histories through comparator and refinement macros. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter
open GreedyMerge.StateLabels

theorem prepare_snapshots {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (start : ℕ) (states : States n)
    (history : LabelHistory.History (External n)) (snapshots : HeapSnapshots history states) :
    HeapSnapshots history (AdministrationJournal.prepare profile tree plan start states).states := by
  cases plan with
  | quiet parents => exact rebase_snapshots before after _ (allocated_preparation_snapshots profile start [] ∅ states snapshots)
  | junction certificate =>
      exact rebase_snapshots before after _ (junction_snapshots _ _ _ _ _ _
        (allocated_preparation_snapshots profile start _ _ states snapshots))

theorem prepare_chronology {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (clock start : ℕ) (states : States n)
    (chronology : Chronology clock states) :
    Chronology clock (AdministrationJournal.prepare profile tree plan start states).states := by
  have prepared (ports : List ℕ) (owners : Finset (External n)) :
      Chronology clock (allocateComparatorPreparation profile ports owners start states).states := by
    rw [← allocateComparatorPreparation_eq]
    exact prepareComparator_chronology profile _ _ ports owners clock states chronology
  cases plan with
  | quiet parents => exact rebaseAll_chronology before after clock _ (prepared [] ∅)
  | junction certificate =>
      apply rebaseAll_chronology before after clock
      rw [allocateJunction_eq]
      exact moveJunction_chronology _ _ _ _ _ clock _ (prepared _ _)

noncomputable def planHistory {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n)
    (history : LabelHistory.History (External n)) : LabelHistory.History (External n) :=
  let prepared := AdministrationJournal.prepare profile tree plan start states
  restorationHistory after tree K clock prepared.ports 0 prepared.next prepared.states
    (LabelHistory.update history clock (RestorationJournal.labels after K prepared.states))

theorem plan_sound {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n)
    (history : LabelHistory.History (External n)) (sound : Sound before K clock states history)
    (chronology : Chronology clock states) :
    let result := allocateComparatorPlan profile tree plan (Execution.entryReader after K clock) start states
    Sound after K (clock+4) result.states (planHistory profile tree plan K clock start states history) ∧
      Chronology (clock+4) result.states := by
  let prepared := AdministrationJournal.prepare profile tree plan start states
  have temporal : Chronology (clock+1) prepared.states :=
    (prepare_chronology profile tree plan clock start states chronology).mono (by omega)
  have batch := sound.update (comparator := after)
    (prepare_snapshots profile tree plan start states history sound.snapshots) ((chronology_iff ..).mp temporal).2
  have restored := restoration_sound after tree K clock prepared.ports 0 prepared.next prepared.states _ batch temporal
  have ports : prepared.ports.length ≤ 3 := by
    rw [AdministrationJournal.prepare_ports]
    exact planPorts_length plan
  have bound : clock+1+0+prepared.ports.length ≤ clock+4 := by omega
  have finalSound := restored.1.advance (clock+4) bound
  have finalChronology := restored.2.mono bound
  rw [AdministrationJournal.prepare_restoration] at finalSound finalChronology
  exact ⟨finalSound, finalChronology⟩

noncomputable def refinementHistory {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (clock start : ℕ) (states : States n)
    (history : LabelHistory.History (External n)) : LabelHistory.History (External n) :=
  let detached := (detachPorts comparator (sequenceNames start) (sequenceNames start) (ports.map Fin.val) 0 states).1
  restorationHistory comparator tree K clock ports 0 (start + Fintype.card (Place n)*ports.length) detached
    (LabelHistory.update history clock (RestorationJournal.labels comparator K detached))

theorem refinement_sound {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (few : ports.length ≤ 4) (clock start : ℕ) (states : States n)
    (history : LabelHistory.History (External n)) (sound : Sound comparator K clock states history)
    (chronology : Chronology clock states) :
    let result := FreshRecanonicalization.allocate comparator tree ports (Execution.entryReader comparator K clock) start states
    Sound comparator K (clock+5) result.states (refinementHistory comparator tree K ports clock start states history) ∧
      Chronology (clock+5) result.states := by
  let detached := (detachPorts comparator (sequenceNames start) (sequenceNames start) (ports.map Fin.val) 0 states).1
  have temporal : Chronology (clock+1) detached :=
    (detachPorts_chronology comparator _ _ (ports.map Fin.val) 0 clock states chronology).mono (by omega)
  have batch := sound.update (comparator := comparator)
    (detachPorts_snapshots comparator start (ports.map Fin.val) 0 states sound.snapshots)
    ((chronology_iff ..).mp temporal).2
  have restored := restoration_sound comparator tree K clock ports 0
    (start + Fintype.card (Place n)*ports.length) detached _ batch temporal
  have bound : clock+1+0+ports.length ≤ clock+5 := by omega
  exact ⟨restored.1.advance (clock+5) bound, restored.2.mono bound⟩

end Greedy.LabelSnapshots
