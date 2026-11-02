import DynamicOptimality.ColoredWalks.EmbeddingOrder

/-! # Canonical positions of persistent fingers

In an ordered ordinary BST, a present key determines its complete zipper,
including the actual ancestor subtrees. Thus a metric certificate starts
at the maintained physical finger, not merely at an existential position.
-/

namespace DynamicOptimality.ColoredWalks

open ChaCha.MTR

variable {α : Type*} [LinearOrder α]

def seek (key : α) : RawTree α → List (Pointer.Frame α) → Option (Pointer.Cursor α)
  | .empty, _ => none
  | .node left pivot right, frames =>
      if key < pivot then seek key left (.left pivot right::frames)
      else if pivot < key then seek key right (.right left pivot::frames)
      else some ⟨.node left pivot right,frames⟩

theorem focus_ordered {focus : RawTree α} {frames : List (Pointer.Frame α)}
    (ordered : (Pointer.plug focus frames).Ordered) : focus.Ordered := by
  induction frames generalizing focus with
  | nil => exact ordered
  | cons frame frames ih =>
    cases frame with
    | left parent right => exact (ordered_node (ih ordered)).1
    | right left parent => exact (ordered_node (ih ordered)).2.1

theorem seek_plug (key : α) (focus : RawTree α) (frames outside : List (Pointer.Frame α))
    (ordered : (Pointer.plug focus frames).Ordered) (member : key ∈ focus.inorder) :
    seek key (Pointer.plug focus frames) outside = seek key focus (frames++outside) := by
  induction frames generalizing focus outside with
  | nil => rfl
  | cons frame frames ih =>
    cases frame with
    | left parent right =>
      have parentOrdered : Tree.Ordered (.node focus parent right) := focus_ordered ordered
      have below := (ordered_node parentOrdered).2.2.1 key member
      have present : key ∈ (ChaCha.MTR.Tree.node focus parent right).inorder := by simp [Tree.inorder,member]
      rw [show Pointer.plug focus (.left parent right::frames) =
        Pointer.plug (.node focus parent right) frames from rfl,ih _ _ ordered present]
      simp only [seek,if_pos below,List.cons_append]
    | right left parent =>
      have parentOrdered : Tree.Ordered (.node left parent focus) := focus_ordered ordered
      have above := (ordered_node parentOrdered).2.2.2 key member
      have present : key ∈ (ChaCha.MTR.Tree.node left parent focus).inorder := by simp [Tree.inorder,member]
      rw [show Pointer.plug focus (.right left parent::frames) =
        Pointer.plug (.node left parent focus) frames from rfl,ih _ _ ordered present]
      simp only [seek,if_neg (not_lt_of_gt above),if_pos above,List.cons_append]

theorem seek_cursor (cursor : Pointer.Cursor α) (key : α)
    (ordered : cursor.tree.Ordered) (atKey : cursor.focus.rootKey = some key) :
    seek key cursor.tree [] = some cursor := by
  rcases cursor with ⟨focus,frames⟩
  cases focus with
  | empty => simp [Tree.rootKey] at atKey
  | node left pivot right =>
    have same : pivot = key := Option.some.inj atKey
    subst pivot
    change seek key (Pointer.plug (.node left key right) frames) [] = _
    rw [seek_plug key _ frames [] ordered (by simp [Tree.inorder])]
    simp [seek]

theorem cursors_eq_of_key (first last : Pointer.Cursor α) (key : α)
    (sameTree : first.tree = last.tree) (ordered : first.tree.Ordered)
    (firstKey : first.focus.rootKey = some key) (lastKey : last.focus.rootKey = some key) :
    first = last := by
  have firstSeek := seek_cursor first key ordered firstKey
  have lastSeek := seek_cursor last key (sameTree ▸ ordered) lastKey
  rw [sameTree,lastSeek] at firstSeek
  exact (Option.some.inj firstSeek).symm

/-- The supplied fingers are preserved as the exact endpoints. -/
theorem DistanceLE.moves_between {tree : RawTree α} {first last : α} {budget : Nat}
    (path : DistanceLE tree first last budget) (ordered : tree.Ordered)
    (a b : Pointer.Cursor α) (aTree : a.tree = tree) (bTree : b.tree = tree)
    (atFirst : a.focus.rootKey = some first) (atLast : b.focus.rootKey = some last) :
    ∃ cost ≤ budget, Moves a b cost := by
  obtain ⟨c,d,cost,cTree,dTree,cKey,dKey,moves,bounded⟩ := path.moves []
  have cSame : c = a := cursors_eq_of_key c a first (cTree.trans aTree.symm)
    (cTree.symm ▸ ordered) cKey atFirst
  have dSame : d = b := cursors_eq_of_key d b last (dTree.trans bTree.symm)
    (dTree.symm ▸ ordered) dKey atLast
  exact ⟨cost,bounded,cSame ▸ dSame ▸ moves⟩

end DynamicOptimality.ColoredWalks
