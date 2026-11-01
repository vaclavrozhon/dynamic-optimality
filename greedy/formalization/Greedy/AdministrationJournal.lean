import Greedy.RestorationJournal
import UniversalComparatorLabels
import ReparentLabels

/-!
# Concrete administrative journals and their constant budgets

The preparation state is extracted from the literal fresh comparator
program. Its journal first changes the labels to that state, then executes
exactly its paid restorations. Refinement rotations use the same interface.
-/

namespace Greedy.AdministrationJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ComparatorOuter GreedyMerge.StateLabels
open EntryJournal RestorationJournal

structure Preparation (n : ℕ) where
  states : HeapSides n
  next : ℕ
  ports : List (External n)

noncomputable def prepare {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (start : ℕ) (states : HeapSides n) : Preparation n :=
  match plan with
  | .quiet _ =>
      let prepared := allocateComparatorPreparation profile [] ∅ start states
      ⟨rebaseAll before after prepared.states, prepared.next, []⟩
  | .junction certificate =>
      let oldOwner := certificate.node.owner (Snapshot.ofTree before)
      let newOwner := certificate.node.owner (Snapshot.ofTree after)
      let prepared := allocateComparatorPreparation profile (junctionPorts (Snapshot.ofTree before) certificate.node)
        {oldOwner, newOwner} start states
      let moved := allocateJunction oldOwner newOwner certificate.node.lower certificate.node.upper prepared.next prepared.states
      ⟨rebaseAll before after moved.states, moved.next, junctionRecords (Snapshot.ofTree before) certificate.node⟩

theorem prepare_ports {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (start : ℕ) (states : HeapSides n) :
    (prepare profile tree plan start states).ports = planPorts plan := by cases plan <;> rfl

theorem prepare_restoration {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) :
    let prepared := prepare profile tree plan start states
    (freshRestorePorts (Snapshot.ofTree after) tree reader prepared.ports 0 prepared.next prepared.states).states =
      (allocateComparatorPlan profile tree plan reader start states).states := by cases plan <;> rfl

noncomputable def planJournal {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : List (Action (External n)) :=
  let prepared := prepare profile tree plan start states
  administration after tree K reader prepared.ports 0 prepared.next prepared.states

theorem plan_spec {n a b depth : ℕ} {before after : BST 0 n}
    (rotation : GreedyMerge.KeyRotationAt a b depth before after)
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b) (H : ℕ)
    (oldHeight : ∀ record : External n, before.externalDepth record.val ≤ H)
    (height : ∀ record : External n, after.externalDepth record.val ≤ H)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage states record owner, (reader stage states record owner).key = record.val)
    (start : ℕ) (states : HeapSides n) (ready : Ready before tree states)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels before (contractedGap H) states) :
    let actions := planJournal profile tree plan (contractedGap H) reader start states
    let result := allocateComparatorPlan profile tree plan reader start states
    EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels after (contractedGap H) result.states ∧
      total ordinary state actions ≤ 3 ∧
      total positiveChange state actions ≤ 6 * ((contractedGap H : ℤ) - 1) := by
  let prepared := prepare profile tree plan start states
  let result := allocateComparatorPlan profile tree plan reader start states
  have entryKey := allocateComparatorPlan_entry_property profile tree plan reader
    (fun _ record _ entry => entry.key = record.val) readerKey start states
  have free : ∀ record, record ∉ prepared.ports →
      labels after (contractedGap H)
        (freshRestorePorts (Snapshot.ofTree after) tree reader prepared.ports 0 prepared.next prepared.states).states record ≤
          labels before (contractedGap H) states record := by
    intro record outside
    rw [prepare_restoration]
    change label _ _ _ _ ≤ _
    rw [← allocateComparatorPlan_eq profile tree plan reader start states]
    apply executeComparatorPlan_label_le rotation profile tree plan result.families result.ids result.bulkNames
      result.paidNames result.makeEntry entryKey states ready
    intro member
    obtain ⟨port, member, equal⟩ := List.mem_map.mp member
    apply outside
    rw [prepare_ports]
    exact (Fin.ext equal : port = record) ▸ member
  have spec := administration_spec before after tree H oldHeight height reader readerKey prepared.ports 0 prepared.next
    states prepared.states free state agree
  dsimp only at spec
  rw [prepare_restoration] at spec
  have ports : prepared.ports.length ≤ 3 := by rw [prepare_ports]; exact planPorts_length plan
  have cap : 0 ≤ (contractedGap H : ℤ) - 1 := by unfold contractedGap; omega
  refine ⟨spec.1, spec.2.1, ?_, ?_⟩
  · have cast : (prepared.ports.length : ℤ) ≤ 3 := by exact_mod_cast ports
    exact spec.2.2.1.trans cast
  · have cast : (prepared.ports.length : ℤ) ≤ 3 := by exact_mod_cast ports
    change total positiveChange state (administration after tree (contractedGap H) reader
      prepared.ports 0 prepared.next prepared.states) ≤ _
    nlinarith [spec.2.2.2]

noncomputable def refinement {n : ℕ} (comparator afterTree : BST 0 n) (K : ℤ)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : List (Action (External n)) :=
  let names : NameSupply n := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  administration comparator afterTree K reader ports 0 (start + Fintype.card (Place n) * ports.length) detached

theorem refinement_spec {n : ℕ} (comparator afterTree : BST 0 n) (H : ℕ)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage states record owner, (reader stage states record owner).key = record.val)
    (start : ℕ) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator (contractedGap H) states) :
    let actions := refinement comparator afterTree (contractedGap H) ports reader start states
    let result := FreshRecanonicalization.allocate comparator afterTree ports reader start states
    EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels comparator (contractedGap H) result.states ∧
      total ordinary state actions ≤ ports.length ∧
      total positiveChange state actions ≤ 2 * ((contractedGap H : ℤ) - 1) * ports.length := by
  let names : NameSupply n := sequenceNames start
  let detached := (detachPorts comparator names names (ports.map Fin.val) 0 states).1
  apply administration_spec comparator comparator afterTree H height height reader readerKey ports 0
    (start + Fintype.card (Place n) * ports.length) states detached _ state agree
  intro record outside
  rw [restore_labels_outside comparator afterTree (contractedGap H) reader readerKey ports 0 _ detached record outside]
  change label _ _ _ _ ≤ _
  apply le_of_eq
  apply detachPorts_label comparator (contractedGap H) names names (ports.map Fin.val) 0 states record.val
  intro member
  obtain ⟨port, member, equal⟩ := List.mem_map.mp member
  exact outside ((Fin.ext equal : port = record) ▸ member)

end Greedy.AdministrationJournal
