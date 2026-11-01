import Greedy.TicketRestoration
import Greedy.PreparationMemory

/-! Literal membership annotations through comparator and refinement macros. -/

namespace Greedy.MembershipStamps

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter

theorem prepare_property {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (start : ℕ) (states : States n)
    (property : Entry → ℕ → Prop) (held : Held property states) :
    Held property (AdministrationJournal.prepare profile tree plan start states).states := by
  cases plan with
  | quiet parents => exact rebase_property before after _ (allocated_preparation_property profile start [] ∅ states held)
  | junction certificate =>
      exact rebase_property before after _ (junction_property _ _ _ _ _ _
        (allocated_preparation_property profile start _ _ states held))

end Greedy.MembershipStamps


namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter
open GreedyMerge.BlockCoverage (Represented)
open WinnerCredit

noncomputable def plan {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n) : List (Action n) :=
  let prepared := AdministrationJournal.prepare profile tree plan start states
  administration after tree K (Execution.entryReader after K clock) prepared.ports 0 prepared.next prepared.states

theorem plan_erases {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (selected : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n) :
    erase (plan profile tree selected K clock start states) =
      AdministrationJournal.planJournal profile tree selected K (Execution.entryReader after K clock) start states :=
  administration_erases ..

theorem plan_administrative {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (selected : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n) :
    Administrative (plan profile tree selected K clock start states) := administration_administrative _ _ _ _ _ _ _ _

theorem plan_pointer {n a b depth : ℕ} {before after : BST 0 n}
    (rotation : GreedyMerge.KeyRotationAt a b depth before after)
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (selected : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n)
    (ready : Ready before tree states) (state : State n) (synced : MembershipPointer.Synced state.ticket states) :
    MembershipPointer.Synced (WinnerCredit.run state (plan profile tree selected K clock start states)).ticket
      (allocateComparatorPlan profile tree selected (Execution.entryReader after K clock) start states).states := by
  have prepared := MembershipStamps.prepare_property profile tree selected start states _ synced
  have spatial := LiveMemory.prepare_spatial rotation profile tree selected start states ready
  have restored := administration_pointer after tree K (Execution.entryReader after K clock)
    (by intros; rfl) _ spatial.2.1 0 (AdministrationJournal.prepare profile tree selected start states).next
    _ spatial.1 spatial.2.2 state prepared
  rw [AdministrationJournal.prepare_restoration] at restored
  exact restored

noncomputable def refinement {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (clock start : ℕ) (states : States n) : List (Action n) :=
  let names : NameSupply n := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  administration comparator tree K (Execution.entryReader comparator K clock) ports 0
    (start + Fintype.card (Place n) * ports.length) detached

theorem refinement_erases {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (clock start : ℕ) (states : States n) :
    erase (refinement comparator tree K ports clock start states) =
      AdministrationJournal.refinement comparator tree K ports (Execution.entryReader comparator K clock) start states :=
  administration_erases ..

theorem refinement_administrative {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (clock start : ℕ) (states : States n) :
    Administrative (refinement comparator tree K ports clock start states) := administration_administrative _ _ _ _ _ _ _ _

theorem refinement_pointer {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (distinct : ports.Nodup) (clock start : ℕ) (states : States n)
    (ordered : Ordered states) (state : State n) (synced : MembershipPointer.Synced state.ticket states) :
    MembershipPointer.Synced (WinnerCredit.run state (refinement comparator tree K ports clock start states)).ticket
      (FreshRecanonicalization.allocate comparator tree ports (Execution.entryReader comparator K clock) start states).states := by
  let names : NameSupply n := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  have detachedPointer := MembershipStamps.detachPorts_property comparator start (ports.map Fin.val) 0 states synced
  have detachedOrdered := detachPorts_valid comparator names names (ports.map Fin.val) 0 states ordered
  have absent : ∀ record ∈ ports, ¬ Represented detached record.val := by
    intro record selected ⟨owner, side, entry, member, key⟩
    have avoided := (detachPorts_membership comparator names names (ports.map Fin.val) 0 states owner side entry).mp member
    exact avoided.2 (List.mem_map.mpr ⟨record, selected, key.symm⟩)
  exact administration_pointer comparator tree K (Execution.entryReader comparator K clock)
    (by intros; rfl) ports distinct 0 _ detached detachedOrdered absent state detachedPointer

end Greedy.TicketJournal
