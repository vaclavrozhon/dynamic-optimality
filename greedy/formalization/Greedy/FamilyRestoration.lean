import Greedy.FamilyConversions
import Greedy.FamilyPaid

/-! Actual-parent paid restoration uses fresh, globally exclusive families. -/

namespace Greedy.FamilyNames

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem restorePort_inventory {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (start : ℕ) (states : HeapSides n)
    (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1
      (restoreNext snapshot tree record start states) := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa only [restorePort, restoreNext, parent] using inventory
  | some owner =>
      let side := decide (record.val < owner.val)
      let slot := encode n (owner, side)
      have supplied := freshPaidSlot_inventory slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states) inventory
      have receiver : table states slot = states owner side := by simp [table, slot]
      have mapped : HeapFamilyInventory
          (heap (GreedyMerge.FreshIds.freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).1)
          (GreedyMerge.FreshIds.freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).2 := by
        simpa only [HeapFamilyInventory, table_heap] using supplied
      dsimp only [GreedyMerge.FreshIds.freshPaidSlot] at mapped
      rw [receiver, heap_update] at mapped
      simpa only [restorePort, portNames, restoreNext, parent, GreedyMerge.FreshIds.freshPaidInsertion] using mapped

theorem restoration_inventory {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (freshRestorePorts snapshot tree reader ports stage start states).states
      (freshRestorePorts snapshot tree reader ports stage start states).next := by
  induction ports generalizing stage start states with
  | nil => exact inventory
  | cons record rest ih =>
      exact ih (stage+1) _ _ (restorePort_inventory snapshot tree record (reader stage states record) start states inventory)

end Greedy.FamilyNames
