import Greedy.FamilyPreparation
import Greedy.FamilyRestoration
import Greedy.FreshRecanonicalization

/-! Family exclusivity for both actual administration macros. -/

namespace Greedy.FamilyNames

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation GreedyMerge.ComparatorOuter

theorem comparator_inventory {n a b depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (tree : BST 0 n)
    (plan : RotationPlan before after tree a b)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (allocateComparatorPlan profile tree plan reader start states).states
      (allocateComparatorPlan profile tree plan reader start states).next := by
  cases plan with
  | quiet parents =>
      exact rebase_inventory before after _ (allocated_preparation_inventory profile start [] ∅ states inventory)
  | junction certificate =>
      exact restoration_inventory (Snapshot.ofTree after) tree reader _ 0 _ _
        (rebase_inventory before after _ (junction_inventory _ _ _ _ _ _
          (allocated_preparation_inventory profile start _ _ states inventory)))

theorem refinement_inventory {n : ℕ} (comparator tree : BST 0 n)
    (ports : List (External n)) (reader : ℕ → HeapSides n → External n → External n → Entry)
    (start : ℕ) (states : HeapSides n) (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (FreshRecanonicalization.allocate comparator tree ports reader start states).states
      (FreshRecanonicalization.allocate comparator tree ports reader start states).next := by
  apply restoration_inventory
  simpa only [List.length_map, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
    detachPorts_inventory comparator start (ports.map Fin.val) 0 states (by simpa using inventory)

end Greedy.FamilyNames
