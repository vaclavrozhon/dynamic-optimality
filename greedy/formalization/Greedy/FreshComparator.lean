import FreshComparatorExecution
import ComparatorHistories

/-!
# A comparator rotation with one fresh, chronological execution

The pivot keys and cut profile come from the actual BST rotation.
The fresh allocator supplies the names and the paid entries. Spatial
invariants, immutable timestamps, inventory, and the birth journal all
refer to this same concrete macro.
-/

namespace Greedy.FreshComparator

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.ComparatorOuter

noncomputable def allocate {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : GreedyMerge.HeapAllocation.FreshComparator n :=
  let input := comparatorInput rotation
  allocateComparatorPlan input.profile tree (rotationPlan input.step tree) reader start states

noncomputable def birthJournal {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) : List ℕ :=
  let input := comparatorInput rotation
  let result := allocate rotation tree reader start states
  executeComparatorPlanIds input.profile tree (rotationPlan input.step tree)
    result.families result.ids result.bulkNames result.paidNames result.makeEntry states

theorem allocate_eq {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) :
    let result := allocate rotation tree reader start states
    (administerActualComparator rotation tree result.families result.ids result.bulkNames
      result.paidNames result.makeEntry states).1 = result.states :=
  allocateComparatorPlan_eq (comparatorInput rotation).profile tree
    (rotationPlan (comparatorInput rotation).step tree) reader start states

theorem rotation_spec {n depth : ℕ} {before after : BST 0 n}
    (rotation : RotationAt depth before after) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage current record owner, (reader stage current record owner).key = record.val)
    (clock : ℕ)
    (readerTime : ∀ stage current record owner, (reader stage current record owner).joined = clock + stage)
    (start : ℕ) (states : HeapSides n) (ready : Ready before tree states)
    (chronology : Chronology clock states) (inventory : HeapInventory states start) :
    let result := allocate rotation tree reader start states
    let journal := birthJournal rotation tree reader start states
    Ready after tree result.states ∧ Chronology (clock + 3) result.states ∧
      HeapInventory result.states result.next ∧ start ≤ result.next ∧
      journal.length ≤ 4*(depth+2)^2+23 ∧ SupportsIds states result.states journal := by
  let input := comparatorInput rotation
  let result := allocate rotation tree reader start states
  have spec := allocateComparatorPlan_spec input.step input.profile tree (rotationPlan input.step tree)
    reader readerKey start states ready inventory
  have time : ∀ stage record owner, (result.makeEntry stage record owner).joined = clock + stage :=
    allocateComparatorPlan_entry_property input.profile tree (rotationPlan input.step tree) reader
      (fun stage _ _ entry => entry.joined = clock + stage) readerTime start states
  obtain ⟨histories, beforeClock⟩ := (chronology_iff clock states).mp chronology
  have temporal := administerActualComparator_chronology rotation tree result.families result.ids
    result.bulkNames result.paidNames result.makeEntry clock states histories beforeClock time
  rw [allocate_eq rotation tree reader start states] at temporal
  exact ⟨spec.1, (chronology_iff ..).mpr temporal, spec.2.1, spec.2.2.1, spec.2.2.2⟩

end Greedy.FreshComparator
