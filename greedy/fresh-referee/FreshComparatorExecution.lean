import FreshFullPreparation
import FreshJunctionTransfer
import FreshPortRestoration

/-!
A complete universally fresh comparator administration. All instance and
family names are computed from the evolving state and a monotone reserved
counter; all paid entries are read from the actual pre-insertion state.
The result is proved equal to the previously checked ordered macro.
-/
namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds Primitives
open GreedyMerge.ComparatorOuter (RotationPlan rotationPlan)
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

structure FreshComparator (n : ℕ) where
  families : NameSupply n
  ids : NameSupply n
  bulkNames : Bool → ℕ
  paidNames : ℕ → PaidNames
  makeEntry : ℕ → External n → External n → Entry
  states : HeapSides n
  next : ℕ

noncomputable def allocateComparatorPlan {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : FreshComparator n :=
  match plan with
  | .quiet _ =>
      let prepared := allocateComparatorPreparation profile [] ∅ start states
      ⟨prepared.families,prepared.ids,fun _ => prepared.next,
        fun _ => ⟨prepared.next,prepared.next,prepared.next,prepared.next,prepared.next⟩,
        fun query => reader query states,rebaseAll before after prepared.states,prepared.next⟩
  | .junction certificate =>
      let oldOwner := certificate.node.owner (Snapshot.ofTree before)
      let newOwner := certificate.node.owner (Snapshot.ofTree after)
      let prepared := allocateComparatorPreparation profile (junctionPorts (Snapshot.ofTree before) certificate.node)
        {oldOwner,newOwner} start states
      let moved := allocateJunction oldOwner newOwner certificate.node.lower certificate.node.upper prepared.next prepared.states
      let rebased := rebaseAll before after moved.states
      let restored := freshRestorePorts (Snapshot.ofTree after) tree reader
        (junctionRecords (Snapshot.ofTree before) certificate.node) 0 moved.next rebased
      ⟨prepared.families,prepared.ids,moved.names,restored.names,restored.makeEntry,restored.states,restored.next⟩

theorem rebaseAll_inventory {n : ℕ} (before after : BST 0 n) (states : HeapSides n) (next : ℕ)
    (inventory : HeapInventory states next) : HeapInventory (rebaseAll before after states) next := by
  apply heapInventory_of_liveIds_eq states _ next _ inventory
  intro owner side
  exact rebaseSide_liveIds before.externalDepth after.externalDepth owner.val (states owner side)

/-- The fresh program realizes precisely the ordered comparator macro with
its returned literal names and immutable entry factory. -/
theorem allocateComparatorPlan_eq {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) :
    let result := allocateComparatorPlan profile tree plan reader start states
    (executeComparatorPlan profile tree plan result.families result.ids result.bulkNames result.paidNames result.makeEntry states).1 = result.states := by
  cases plan with
  | quiet parents =>
      change rebaseAll before after
        (prepareComparator profile (allocateComparatorPreparation profile [] ∅ start states).families
          (allocateComparatorPreparation profile [] ∅ start states).ids [] ∅ states).1 = _
      rw [allocateComparatorPreparation_eq]
      rfl
  | junction certificate =>
      let oldOwner := certificate.node.owner (Snapshot.ofTree before)
      let newOwner := certificate.node.owner (Snapshot.ofTree after)
      let ports := junctionRecords (Snapshot.ofTree before) certificate.node
      let prepared := allocateComparatorPreparation profile (ports.map Fin.val) {oldOwner,newOwner} start states
      let moved := allocateJunction oldOwner newOwner certificate.node.lower certificate.node.upper prepared.next prepared.states
      let restored := freshRestorePorts (Snapshot.ofTree after) tree reader ports 0 moved.next
        (rebaseAll before after moved.states)
      change (restorePorts (Snapshot.ofTree after) tree restored.names restored.makeEntry ports 0
        (rebaseAll before after (moveJunction oldOwner newOwner certificate.node.lower certificate.node.upper moved.names
          (prepareComparator profile prepared.families prepared.ids (ports.map Fin.val) {oldOwner,newOwner} states).1))).1 = restored.states
      rw [allocateComparatorPreparation_eq]
      rw [←allocateJunction_eq]
      exact freshRestorePorts_eq (Snapshot.ofTree after) tree reader ports 0 moved.next _

theorem allocateComparatorPlan_inventory {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (allocateComparatorPlan profile tree plan reader start states).states
      (allocateComparatorPlan profile tree plan reader start states).next := by
  cases plan with
  | quiet parents =>
      exact rebaseAll_inventory before after _ _ (allocateComparatorPreparation_inventory profile [] ∅ start states inventory)
  | junction certificate =>
      exact freshRestorePorts_inventory (Snapshot.ofTree after) tree reader _ 0 _ _
        (rebaseAll_inventory before after _ _ (allocateJunction_inventory _ _ certificate.different _ _ _ _
          (allocateComparatorPreparation_inventory profile _ _ start states inventory)))

theorem allocateComparatorPlan_monotone {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : start≤(allocateComparatorPlan profile tree plan reader start states).next := by
  cases plan with
  | quiet parents => exact allocateComparatorPreparation_monotone profile [] ∅ start states
  | junction certificate =>
      exact (allocateComparatorPreparation_monotone profile _ _ start states).trans
        ((allocateJunction_monotone _ _ _ _ _ _).trans (freshRestorePorts_monotone (Snapshot.ofTree after) tree reader _ 0 _ _))

theorem allocateComparatorPlan_entry_property {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (property : ℕ → External n → External n → Entry → Prop)
    (readerProperty : ∀ stage current record owner, property stage record owner (reader stage current record owner))
    (start : ℕ) (states : HeapSides n) :
    ∀ stage record owner, property stage record owner
      ((allocateComparatorPlan profile tree plan reader start states).makeEntry stage record owner) := by
  cases plan with
  | quiet parents => exact fun stage record owner => readerProperty stage states record owner
  | junction certificate =>
      dsimp only [allocateComparatorPlan]
      exact freshRestorePorts_entry_property (Snapshot.ofTree after) tree reader property readerProperty _ 0 _ _

/-- Full spatial/numerical closure and actual global live-ID freshness.
Only the old state invariants and the reader's physical-key equation are
premises; no fresh-name assignment or aggregate birth budget is assumed. -/
theorem allocateComparatorPlan_spec {n a b depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt a b depth before after) (profile : RotationCutProfile before after depth)
    (tree : BST 0 n) (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage current record owner, (reader stage current record owner).key=record.val)
    (start : ℕ) (states : HeapSides n) (ready : Ready before tree states) (inventory : HeapInventory states start) :
    let result := allocateComparatorPlan profile tree plan reader start states
    Ready after tree result.states ∧ HeapInventory result.states result.next ∧ start≤result.next ∧
      (executeComparatorPlanIds profile tree plan result.families result.ids result.bulkNames result.paidNames result.makeEntry states).length
        ≤ 4*(depth+2)^2+23 ∧
      SupportsIds states result.states
        (executeComparatorPlanIds profile tree plan result.families result.ids result.bulkNames result.paidNames result.makeEntry states) := by
  let result := allocateComparatorPlan profile tree plan reader start states
  have key : ∀ stage record owner,(result.makeEntry stage record owner).key=record.val :=
    allocateComparatorPlan_entry_property profile tree plan reader (fun _ record _ entry => entry.key=record.val) readerKey start states
  have exactState := allocateComparatorPlan_eq profile tree plan reader start states
  change (executeComparatorPlan profile tree plan result.families result.ids result.bulkNames result.paidNames result.makeEntry states).1=result.states at exactState
  have spec := executeComparatorPlan_spec step profile tree plan result.families result.ids result.bulkNames result.paidNames
    result.makeEntry key states ready
  have support := executeComparatorPlan_id_support profile tree plan result.families result.ids result.bulkNames result.paidNames result.makeEntry states
  refine ⟨?_,allocateComparatorPlan_inventory profile tree plan reader start states inventory,
    allocateComparatorPlan_monotone profile tree plan reader start states,?_,?_⟩
  · rw [exactState] at spec
    exact spec.1
  · rw [executeComparatorPlanIds_length]
    exact spec.2
  · rw [exactState] at support
    exact support

#print axioms allocateComparatorPlan_eq
#print axioms allocateComparatorPlan_inventory
#print axioms allocateComparatorPlan_spec

end GreedyMerge.HeapAllocation
