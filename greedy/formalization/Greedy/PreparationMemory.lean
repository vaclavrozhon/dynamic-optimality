import Greedy.RestorationMemory
import Greedy.HistoryAdministration

/-! Comparator preparation preserves memories and detaches every paid port. -/

namespace Greedy.EntryProperties

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

end Greedy.EntryProperties

namespace Greedy.LiveMemory

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter
open GreedyMerge.BlockCoverage (Represented)
open EntryJournal RestorationJournal

theorem prepare_spatial {n a b depth : ℕ} {before after : BST 0 n}
    (rotation : GreedyMerge.KeyRotationAt a b depth before after)
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (start : ℕ) (states : States n)
    (ready : Ready before tree states) :
    let prepared := AdministrationJournal.prepare profile tree plan start states
    Ordered prepared.states ∧ prepared.ports.Nodup ∧
      (∀ record ∈ prepared.ports, ¬ Represented prepared.states record.val) := by
  cases plan with
  | quiet parents =>
      refine ⟨?_, List.nodup_nil, by simp [AdministrationJournal.prepare]⟩
      apply rebaseAll_valid before after
      rw [← allocateComparatorPreparation_eq]
      exact prepareComparator_valid profile _ _ [] ∅ states ready.valid
  | junction certificate =>
      let oldOwner := certificate.node.owner (Snapshot.ofTree before)
      let newOwner := certificate.node.owner (Snapshot.ofTree after)
      let ports := junctionRecords (Snapshot.ofTree before) certificate.node
      let prepared := allocateComparatorPreparation profile (junctionPorts (Snapshot.ofTree before) certificate.node) {oldOwner, newOwner} start states
      let moved := allocateJunction oldOwner newOwner certificate.node.lower certificate.node.upper prepared.next prepared.states
      have spatial := prepareMoveJunction_spec rotation profile tree certificate.node certificate.occurrence certificate.separated
        oldOwner newOwner certificate.oldValue certificate.newValue rfl rfl certificate.different
        prepared.families prepared.ids moved.names states ready.valid ready.sound ready.complete ready.persistent
      dsimp only [prepareMoveJunction] at spatial
      rw [allocateComparatorPreparation_eq profile (junctionPorts (Snapshot.ofTree before) certificate.node) {oldOwner, newOwner} start states] at spatial
      rw [← allocateJunction_eq oldOwner newOwner certificate.node.lower certificate.node.upper prepared.next prepared.states] at spatial
      refine ⟨rebaseAll_valid before after moved.states spatial.1,
        junctionRecords_distinct _ _, ?_⟩
      intro record selected ⟨owner, side, entry, member, key⟩
      apply spatial.2.2.2.1 record.val (List.mem_map.mpr ⟨record, selected, rfl⟩)
      exact ⟨owner, side, entry, by simpa only [AdministrationJournal.prepare, rebaseAll_entries] using member, key⟩

theorem plan {n a b depth : ℕ} {before after : BST 0 n}
    (rotation : GreedyMerge.KeyRotationAt a b depth before after)
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ) (clock start : ℕ) (states : States n)
    (ready : Ready before tree states) (state : WeightedMemory.State (External n))
    (synced : Synced state.memory states) :
    Synced (run state (AdministrationJournal.planJournal profile tree plan K
      (Execution.entryReader after K clock) start states)).memory
      (allocateComparatorPlan profile tree plan (Execution.entryReader after K clock) start states).states ∧
    Ordered (allocateComparatorPlan profile tree plan (Execution.entryReader after K clock) start states).states := by
  have prepared := EntryProperties.prepare_property profile tree plan start states _ synced
  have spatial := prepare_spatial rotation profile tree plan start states ready
  have restored := administration after tree K (Execution.entryReader after K clock)
    (by intros; rfl) (by intros; rfl) _ spatial.2.1 0
    (AdministrationJournal.prepare profile tree plan start states).next _ spatial.1 spatial.2.2 state prepared
  rw [AdministrationJournal.prepare_restoration] at restored
  exact restored

theorem refinement {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (distinct : ports.Nodup) (clock start : ℕ) (states : States n)
    (ordered : Ordered states) (state : WeightedMemory.State (External n)) (synced : Synced state.memory states) :
    Synced (run state (AdministrationJournal.refinement comparator tree K ports
      (Execution.entryReader comparator K clock) start states)).memory
      (FreshRecanonicalization.allocate comparator tree ports
        (Execution.entryReader comparator K clock) start states).states ∧
    Ordered (FreshRecanonicalization.allocate comparator tree ports
        (Execution.entryReader comparator K clock) start states).states := by
  let names : NameSupply n := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  have detachedMemory := EntryProperties.detachPorts_property comparator start (ports.map Fin.val) 0 states synced
  have detachedOrdered := detachPorts_valid comparator names names (ports.map Fin.val) 0 states ordered
  have absent : ∀ record ∈ ports, ¬ Represented detached record.val := by
    intro record selected ⟨owner, side, entry, member, key⟩
    have avoided := (detachPorts_membership comparator names names (ports.map Fin.val) 0 states owner side entry).mp member
    exact avoided.2 (List.mem_map.mpr ⟨record, selected, key.symm⟩)
  exact administration comparator tree K (Execution.entryReader comparator K clock)
    (by intros; rfl) (by intros; rfl) ports distinct 0 _ detached detachedOrdered absent state detachedMemory

end Greedy.LiveMemory
