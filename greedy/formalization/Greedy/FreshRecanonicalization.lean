import FreshComparatorPreparation
import FreshPortRestoration
import RecanonicalizationHistories

/-!
# Fresh execution of fixed-comparator refinement rotations

Recanonicalization changes at most four actual parents per rotation.
This module executes the existing detach/restore program with names
allocated from the evolving global inventory. Each paid entry reads the
state immediately before insertion. The ready-state, clock, and birth
budget proofs apply to this same execution.
-/

namespace Greedy.FreshRecanonicalization

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PortCases

structure Result (n : ℕ) where
  names : NameSupply n
  paidNames : ℕ → PaidNames
  makeEntry : ℕ → External n → External n → Entry
  states : HeapSides n
  next : ℕ

noncomputable def allocate {n : ℕ} (comparator afterTree : BST 0 n)
    (ports : List (External n))
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : Result n :=
  let names := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  let next := start + Fintype.card (Place n) * ports.length
  let restored := freshRestorePorts (Snapshot.ofTree comparator) afterTree reader ports 0 next detached
  ⟨names, restored.names, restored.makeEntry, restored.states, restored.next⟩

theorem allocate_eq {n : ℕ} (comparator afterTree : BST 0 n)
    (ports : List (External n))
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) :
    let result := allocate comparator afterTree ports reader start states
    (reparentSelected comparator afterTree result.names result.names result.paidNames
      result.makeEntry ports states).1 = result.states := by
  exact freshRestorePorts_eq (Snapshot.ofTree comparator) afterTree reader ports 0 _ _

theorem allocate_inventory {n : ℕ} (comparator afterTree : BST 0 n)
    (ports : List (External n))
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (allocate comparator afterTree ports reader start states).states
      (allocate comparator afterTree ports reader start states).next := by
  apply freshRestorePorts_inventory
  simpa only [List.length_map, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
    detachPorts_fresh_inventory comparator start (ports.map Fin.val) 0 states (by simpa using inventory)

theorem allocate_monotone {n : ℕ} (comparator afterTree : BST 0 n)
    (ports : List (External n))
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) :
    start ≤ (allocate comparator afterTree ports reader start states).next :=
  (Nat.le_add_right _ _).trans (freshRestorePorts_monotone (Snapshot.ofTree comparator) afterTree reader ports 0 _ _)

theorem allocate_entry_property {n : ℕ} (comparator afterTree : BST 0 n)
    (ports : List (External n))
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (property : ℕ → External n → External n → Entry → Prop)
    (readerProperty : ∀ stage current record owner, property stage record owner (reader stage current record owner))
    (start : ℕ) (states : HeapSides n) :
    ∀ stage record owner, property stage record owner
      ((allocate comparator afterTree ports reader start states).makeEntry stage record owner) :=
  freshRestorePorts_entry_property (Snapshot.ofTree comparator) afterTree reader property readerProperty ports 0 _ _

theorem rotation_spec {n depth : ℕ} (comparator : BST 0 n)
    {beforeTree afterTree : BST 0 n} (rotation : RotationAt depth beforeTree afterTree)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage current record owner, (reader stage current record owner).key = record.val)
    (clock : ℕ)
    (readerTime : ∀ stage current record owner, (reader stage current record owner).joined = clock + stage)
    (start : ℕ) (states : HeapSides n) (ready : Ready comparator beforeTree states)
    (chronology : Chronology clock states) (inventory : HeapInventory states start) :
    let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
    let result := allocate comparator afterTree ports reader start states
    let journal := reparentSelectedIds comparator afterTree result.names result.names result.paidNames
      result.makeEntry ports states
    Ready comparator afterTree result.states ∧ Chronology (clock + 4) result.states ∧
      HeapInventory result.states result.next ∧ start ≤ result.next ∧
      journal.length ≤ 20 ∧ SupportsIds states result.states journal := by
  let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
  let result := allocate comparator afterTree ports reader start states
  have key : ∀ stage record owner, (result.makeEntry stage record owner).key = record.val :=
    allocate_entry_property comparator afterTree ports reader (fun _ record _ entry => entry.key = record.val)
      readerKey start states
  have time : ∀ stage record owner, (result.makeEntry stage record owner).joined = clock + stage :=
    allocate_entry_property comparator afterTree ports reader (fun stage _ _ entry => entry.joined = clock + stage)
      readerTime start states
  have equal := allocate_eq comparator afterTree ports reader start states
  have spatial := administerRefinementRotation_ready comparator rotation result.names result.names
    result.paidNames result.makeEntry key states ready
  have temporal := administerRefinementRotation_chronology comparator rotation result.names result.names
    result.paidNames result.makeEntry clock states chronology time
  change Ready comparator afterTree
      (reparentSelected comparator afterTree result.names result.names result.paidNames result.makeEntry ports states).1 ∧
      (reparentSelected comparator afterTree result.names result.names result.paidNames result.makeEntry ports states).2 ≤ 20
    at spatial
  change Chronology (clock + 4)
      (reparentSelected comparator afterTree result.names result.names result.paidNames result.makeEntry ports states).1
    at temporal
  rw [equal] at spatial temporal
  refine ⟨spatial.1, temporal, allocate_inventory comparator afterTree ports reader start states inventory,
    allocate_monotone comparator afterTree ports reader start states, ?_, ?_⟩
  · rw [reparentSelectedIds_length]
    exact spatial.2
  · rw [← equal]
    exact reparentSelected_id_support comparator afterTree result.names result.names result.paidNames result.makeEntry ports states

structure Frame (n : ℕ) where
  tree : BST 0 n
  states : HeapSides n
  clock : ℕ
  next : ℕ

def Frame.Valid {n : ℕ} (comparator : BST 0 n) (frame : Frame n) : Prop :=
  Ready comparator frame.tree frame.states ∧ Chronology frame.clock frame.states ∧
    HeapInventory frame.states frame.next

abbrev Reader (n : ℕ) := ℕ → ℕ → HeapSides n → External n → External n → Entry

noncomputable def nextFrame {n depth : ℕ} (comparator : BST 0 n) (reader : Reader n)
    (frame : Frame n) (afterTree : BST 0 n) (rotation : RotationAt depth frame.tree afterTree) : Frame n :=
  let result := allocate comparator afterTree (refinementRotationPorts (Snapshot.ofTree comparator) rotation)
    (reader frame.clock) frame.next frame.states
  ⟨afterTree, result.states, frame.clock + 5, result.next⟩

noncomputable def birthJournal {n depth : ℕ} (comparator : BST 0 n) (reader : Reader n)
    (frame : Frame n) (afterTree : BST 0 n) (rotation : RotationAt depth frame.tree afterTree) : List ℕ :=
  let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
  let result := allocate comparator afterTree ports (reader frame.clock) frame.next frame.states
  reparentSelectedIds comparator afterTree result.names result.names result.paidNames result.makeEntry ports frame.states

/-- The witness retains each literal allocator execution, not merely its
final invariant and numerical cost. -/
inductive Execution {n : ℕ} (comparator : BST 0 n) (reader : Reader n) :
    ℕ → Frame n → Frame n → List ℕ → Prop
  | nil (frame : Frame n) : Execution comparator reader 0 frame frame []
  | cons {count depth : ℕ} {first last : Frame n} {middle : BST 0 n} {tail : List ℕ}
      (rotation : RotationAt depth first.tree middle)
      (rest : Execution comparator reader count (nextFrame comparator reader first middle rotation) last tail) :
      Execution comparator reader (count + 1) first last
        (birthJournal comparator reader first middle rotation ++ tail)

theorem execute_steps {n steps : ℕ} (comparator : BST 0 n) (reader : Reader n)
    (readerKey : ∀ clock stage current record owner, (reader clock stage current record owner).key = record.val)
    (readerTime : ∀ clock stage current record owner,
      (reader clock stage current record owner).joined = clock + 1 + stage)
    (first : Frame n) (afterTree : BST 0 n) (rotations : RotationSteps steps first.tree afterTree)
    (valid : first.Valid comparator) :
    ∃ last journal, Execution comparator reader steps first last journal ∧
      last.tree = afterTree ∧ last.Valid comparator ∧ last.clock = first.clock + 5*steps ∧
      first.next ≤ last.next ∧ journal.length ≤ 20*steps ∧ SupportsIds first.states last.states journal := by
  induction steps generalizing first with
  | zero =>
      cases rotations
      exact ⟨first, [], .nil first, rfl, valid, by simp, le_refl _, by simp, supportsIds_refl first.states⟩
  | succ steps ih =>
      cases rotations with
      | @cons _ depth _ _ before middle after rotation rest =>
          have head := rotation_spec comparator rotation (reader first.clock) (readerKey first.clock)
            (first.clock + 1) (readerTime first.clock) first.next first.states valid.1
            (valid.2.1.mono (by omega)) valid.2.2
          let second := nextFrame comparator reader first middle rotation
          have secondValid : second.Valid comparator := ⟨head.1, head.2.1, head.2.2.1⟩
          obtain ⟨last, tail, executed, finalTree, finalValid, finalClock, counter, budget, support⟩ :=
            ih second rest secondValid
          refine ⟨last, birthJournal comparator reader first middle rotation ++ tail,
            .cons rotation executed, finalTree, finalValid, ?_, ?_, ?_, ?_⟩
          · change last.clock = first.clock + 5 + 5*steps at finalClock
            omega
          · exact head.2.2.2.1.trans counter
          · have headBound : (birthJournal comparator reader first middle rotation).length ≤ 20 := head.2.2.2.2.1
            simp only [List.length_append]
            omega
          · exact supportsIds_trans head.2.2.2.2.2 support

end Greedy.FreshRecanonicalization
