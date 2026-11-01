import DynamicOptimality.HullPriorityUpdate

/-! The last-touch heap and a reached rooted hull supply the geometric
witness for a new/old pair: either the old key is touched too, the new
key was touched at least as recently, or another touched key separates
the two keys in their BST order. -/

namespace DynamicOptimality

open TangoSquared TangoSquared.MTR.Tree TangoSquared.MTR.Tree.PriorityHull

variable {α : Type*} [LinearOrder α]

theorem hull_key_separation (source : RawTree α) (gaps : Nat → RawTree α) (start : Nat)
    (priority : α → Int) (heap : Heap priority (graft source gaps start))
    (ordered : Ordered (graft source gaps start)) {new old : α}
    (selected : new ∈ source.inorder) (present : old ∈ (graft source gaps start).inorder) :
    old ∈ source.inorder ∨ priority old ≤ priority new ∨
      ∃ middle ∈ source.inorder, middle ≠ new ∧ middle ≠ old ∧
        min new old ≤ middle ∧ middle ≤ max new old := by
  induction source generalizing start with
  | empty => simp only [inorder,List.not_mem_nil] at selected
  | node left key right ihl ihr =>
    obtain ⟨orderedLeft,orderedRight,leftLt,rightLt⟩ := ordered_node_parts ordered
    simp only [inorder,List.mem_append,List.mem_singleton] at selected
    obtain (newLeft | atRoot) | newRight := selected
    · have newPresent := (inorder_sublist_graft left gaps start).subset newLeft
      have newLt := leftLt new newPresent
      simp only [graft,inorder,List.mem_append,List.mem_singleton] at present
      obtain (oldLeft | oldRoot) | oldRight := present
      · obtain touched | recent | ⟨middle,inLeft,notNew,notOld,between⟩ :=
          ihl start heap.1 orderedLeft newLeft oldLeft
        · exact .inl (by simp [inorder,touched])
        · exact .inr (.inl recent)
        · exact .inr (.inr ⟨middle,by simp [inorder,inLeft],notNew,notOld,between⟩)
      · exact .inl (by simp [inorder,oldRoot])
      · have oldGt := rightLt old oldRight
        exact .inr (.inr ⟨key,by simp [inorder],ne_of_gt newLt,ne_of_lt oldGt,
          (min_le_left _ _).trans newLt.le,oldGt.le.trans (le_max_right _ _)⟩)
    · subst new
      have rootBound : Bounded priority (priority key) (graft (.node left key right) gaps start) :=
        bounded_node.mpr ⟨heap.2.2.1,le_rfl,heap.2.2.2⟩
      exact .inr (.inl (rootBound old present))
    · have newPresent := (inorder_sublist_graft right gaps (start+left.size+1)).subset newRight
      have newGt := rightLt new newPresent
      simp only [graft,inorder,List.mem_append,List.mem_singleton] at present
      obtain (oldLeft | oldRoot) | oldRight := present
      · have oldLt := leftLt old oldLeft
        exact .inr (.inr ⟨key,by simp [inorder],ne_of_lt newGt,ne_of_gt oldLt,
          (min_le_right _ _).trans oldLt.le,newGt.le.trans (le_max_left _ _)⟩)
      · exact .inl (by simp [inorder,oldRoot])
      · obtain touched | recent | ⟨middle,inRight,notNew,notOld,between⟩ :=
          ihr (start+left.size+1) heap.2.1 orderedRight newRight oldRight
        · exact .inl (by simp [inorder,touched])
        · exact .inr (.inl recent)
        · exact .inr (.inr ⟨middle,by simp [inorder,inRight],notNew,notOld,between⟩)

end DynamicOptimality
