import HeapFreshAllocation
import FreshOuterTransfer

/-! The two actual outer-side transfers are allocated sequentially in the
finite owner/side table, and exactly realize the existing moveJunction. -/
namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

structure FreshJunction (n : ℕ) where
  names : Bool → ℕ
  states : HeapSides n
  next : ℕ

noncomputable def allocateJunction {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) : FreshJunction n :=
  let first := freshOuterMove (encode n (oldOwner,false)) (encode n (newOwner,false)) false
    (junctionCut false lo hi) start (table states)
  let second := freshOuterMove (encode n (oldOwner,true)) (encode n (newOwner,true)) true
    (junctionCut true lo hi) first.2 first.1
  ⟨fun side => if side then first.2 else start,heap second.1,second.2⟩

theorem allocateJunction_inventory {n : ℕ} (oldOwner newOwner : External n) (different : oldOwner≠newOwner)
    (lo hi start : ℕ) (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (allocateJunction oldOwner newOwner lo hi start states).states
      (allocateJunction oldOwner newOwner lo hi start states).next := by
  have distinct (side : Bool) : encode n (oldOwner,side)≠encode n (newOwner,side) := by
    intro equal
    exact different (Prod.mk.inj ((encode n).injective equal)).1
  have first := freshOuterMove_inventory (encode n (oldOwner,false)) (encode n (newOwner,false)) (distinct false)
    false (junctionCut false lo hi) start (table states) inventory
  have second := freshOuterMove_inventory (encode n (oldOwner,true)) (encode n (newOwner,true)) (distinct true)
    true (junctionCut true lo hi) _ _ first
  simpa only [HeapInventory,allocateJunction,table_heap] using second

theorem allocateJunction_eq {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) :
    (allocateJunction oldOwner newOwner lo hi start states).states =
      moveJunction oldOwner newOwner lo hi (allocateJunction oldOwner newOwner lo hi start states).names states := by
  classical
  funext owner side
  have encoding (a b : External n × Bool) : encode n a=encode n b ↔ a=b := (encode n).injective.eq_iff
  cases side <;>
    simp [allocateJunction,freshOuterMove,replaceTwo,heap,table,moveJunction,encoding]

theorem allocateJunction_monotone {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) : start≤(allocateJunction oldOwner newOwner lo hi start states).next := by
  change start ≤ (start+2*(table states (encode n (oldOwner,false))).shrinking.length)+_
  omega

theorem allocateJunction_first_name {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) : (allocateJunction oldOwner newOwner lo hi start states).names false=start := rfl

theorem allocateJunction_second_name {n : ℕ} (oldOwner newOwner : External n) (lo hi start : ℕ)
    (states : HeapSides n) : (allocateJunction oldOwner newOwner lo hi start states).names true=
      start+2*(states oldOwner false).shrinking.length := by
  simp [allocateJunction,freshOuterMove,table]

#print axioms allocateJunction_inventory
#print axioms allocateJunction_eq
#print axioms allocateJunction_monotone

end GreedyMerge.HeapAllocation
