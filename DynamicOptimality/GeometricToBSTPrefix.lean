import DynamicOptimality.GeometricToBSTMarked
import DynamicOptimality.GeometricModel

/-!
# Extracting the most recent geometric row

The keys of the newest row have a common priority strictly larger than
every untouched key. They therefore form a rooted prefix in any weak
max-heap of last-touch times. All holes retain their old heap invariant.
-/

namespace DynamicOptimality.Geometry

open ChaCha ChaCha.MTR ChaCha.MTR.Tree
open ChaCha.MTR.Pointer ChaCha.MTR.Tree.PriorityHull

def markRow (row : Finset Nat) : RawTree Nat → MarkedTree Nat
  | .empty => .hole .empty
  | .node left key right =>
      if key ∈ row then .node (markRow row left) key (markRow row right)
      else .hole (.node left key right)

@[simp] theorem markRow_erase (row : Finset Nat) (tree : RawTree Nat) :
    (markRow row tree).erase = tree := by
  induction tree with
  | empty => rfl
  | node left key right ihl ihr =>
      simp only [markRow]
      split <;> simp [MarkedTree.erase, ihl, ihr]

theorem cold_root_cold_subtree {n root : Nat} {height : Nat → Int}
    {time : Int} {row : Finset Nat} {left right : RawTree Nat}
    (heap : Heap (update height time row) (.node left root right))
    (bounded : ∀ key ∈ (ChaCha.MTR.Tree.node left root right).inorder, key < n)
    (above : ∀ key, key < n → height key < time)
    (cold : root ∉ row) :
    ∀ key ∈ (ChaCha.MTR.Tree.node left root right).inorder, key ∉ row := by
  intro key member selected
  have rootBound := bounded root (by simp [inorder])
  have entire : Bounded (update height time row) (update height time row root)
      (.node left root right) := bounded_node.mpr ⟨heap.2.2.1, le_rfl, heap.2.2.2⟩
  have bound := entire key member
  simp only [update, if_pos selected, if_neg cold] at bound
  have strict := above root rootBound
  omega

theorem markRow_members {n : Nat} {height : Nat → Int} {time : Int} {row : Finset Nat}
    (tree : RawTree Nat) (heap : Heap (update height time row) tree)
    (bounded : ∀ key ∈ tree.inorder, key < n)
    (above : ∀ key, key < n → height key < time) :
    ∀ key, key ∈ (markRow row tree).skeleton.inorder ↔ key ∈ row ∧ key ∈ tree.inorder := by
  induction tree with
  | empty => simp [markRow, MarkedTree.skeleton, inorder]
  | node left root right ihl ihr =>
      by_cases selected : root ∈ row
      · have leftBound : ∀ key ∈ left.inorder, key < n := by
          intro key member
          exact bounded key (by simp [inorder, member])
        have rightBound : ∀ key ∈ right.inorder, key < n := by
          intro key member
          exact bounded key (by simp [inorder, member])
        have leftMembers := ihl heap.1 leftBound
        have rightMembers := ihr heap.2.1 rightBound
        intro key
        simp only [markRow, if_pos selected, MarkedTree.skeleton, inorder,
          List.mem_append, List.mem_singleton, leftMembers, rightMembers]
        constructor
        · rintro ((⟨touch, member⟩ | equal) | ⟨touch, member⟩)
          · exact ⟨touch, Or.inl (Or.inl member)⟩
          · subst key; exact ⟨selected, Or.inl (Or.inr rfl)⟩
          · exact ⟨touch, Or.inr member⟩
        · rintro ⟨touch, ((member | equal) | member)⟩
          · exact Or.inl (Or.inl ⟨touch, member⟩)
          · exact Or.inl (Or.inr equal)
          · exact Or.inr ⟨touch, member⟩
      · have cold := cold_root_cold_subtree heap bounded above selected
        intro key
        simp only [markRow, if_neg selected, MarkedTree.skeleton, inorder, List.not_mem_nil, false_iff]
        rintro ⟨touch, member⟩
        exact cold key member touch

theorem markRow_holes_heap {n : Nat} {height : Nat → Int} {time : Int} {row : Finset Nat}
    (tree : RawTree Nat) (heap : Heap (update height time row) tree)
    (bounded : ∀ key ∈ tree.inorder, key < n)
    (above : ∀ key, key < n → height key < time) :
    ∀ hole ∈ (markRow row tree).holes, Heap height hole := by
  induction tree with
  | empty => simp [markRow, MarkedTree.holes, Heap]
  | node left root right ihl ihr =>
      by_cases selected : root ∈ row
      · have leftBound : ∀ key ∈ left.inorder, key < n := by
          intro key member
          exact bounded key (by simp [inorder, member])
        have rightBound : ∀ key ∈ right.inorder, key < n := by
          intro key member
          exact bounded key (by simp [inorder, member])
        intro hole member
        simp only [markRow, if_pos selected, MarkedTree.holes, List.mem_append] at member
        rcases member with member | member
        · exact ihl heap.1 leftBound hole member
        · exact ihr heap.2.1 rightBound hole member
      · have cold := cold_root_cold_subtree heap bounded above selected
        intro hole member
        simp only [markRow, if_neg selected, MarkedTree.holes, List.mem_singleton] at member
        subst hole
        exact heap_congr _ (fun key member => if_neg (cold key member)) heap

end DynamicOptimality.Geometry
