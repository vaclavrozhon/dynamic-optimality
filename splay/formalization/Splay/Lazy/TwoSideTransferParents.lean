import Splay.Lazy.TwoSideTransfer

namespace Splay.Lazy

/-- The moved prefix consists of exactly the source's children on this side,
except for its terminal boundary singleton. -/
theorem SideTransferGeometry.mem_moved_iff {n : ℕ} {view : HeapView n}
    {source boundary : Element n} {side : Side}
    (geometry : SideTransferGeometry view source boundary side) (element : Element n) :
    element ∈ geometry.moved ↔
      view.parent element = some source ∧ view.side element = side ∧ element ≠ boundary := by
  constructor
  · intro member
    exact ⟨(geometry.moved_parent_side member).1, (geometry.moved_parent_side member).2,
      fun equal => geometry.boundary_not_moved (equal ▸ member)⟩
  · rintro ⟨parent, sideEq, different⟩
    have member := view.mem_topDown_iff.mpr ⟨parent, sideEq⟩
    rw [geometry.decomposition] at member
    rcases List.mem_append.mp member with moved | terminal
    · exact moved
    · exact (different (List.mem_singleton.mp terminal)).elim

/-- The exact parent map of the two actual silent transfer steps. -/
theorem State.transferBothSides_parent {n : ℕ} (state : State n) {source left right : Element n}
    (first : SideTransferGeometry state.view source left .left)
    (second : SideTransferGeometry state.view source right .right)
    (ordered : state.view.HeapOrdered) (element : Element n) :
    (state.transferBothSides first second ordered).view.parent element =
      if element ∈ second.moved then some right else
      if element ∈ first.moved then some left else state.view.parent element := by
  change ((first.afterLeft second ordered).after (first.after_ordered ordered)).parent element = _
  rw [SideTransferGeometry.after_parent, SideTransferGeometry.after_parent]
  rfl

/-- The side of every moved child is its transfer side; all other side data
is preserved by the two silent operations. -/
theorem State.transferBothSides_side {n : ℕ} (state : State n) {source left right : Element n}
    (first : SideTransferGeometry state.view source left .left)
    (second : SideTransferGeometry state.view source right .right)
    (ordered : state.view.HeapOrdered) (element : Element n) :
    (state.transferBothSides first second ordered).view.side element =
      if element ∈ second.moved then .right else
      if element ∈ first.moved then .left else state.view.side element := by
  change ((first.afterLeft second ordered).after (first.after_ordered ordered)).side element = _
  rw [SideTransferGeometry.after_side, SideTransferGeometry.after_side]
  rfl

/-- The root's administrative side survives both whole-side transfers. -/
theorem State.transferBothSides_root_side {n : ℕ} (state : State n) {source left right : Element n}
    (first : SideTransferGeometry state.view source left .left)
    (second : SideTransferGeometry state.view source right .right)
    (ordered : state.view.HeapOrdered) :
    (state.transferBothSides first second ordered).view.side state.view.root = state.view.side state.view.root := by
  rw [state.transferBothSides_side first second ordered]
  rw [if_neg (fun member => second.root_not_moved (List.mem_toFinset.mpr member)),
    if_neg (fun member => first.root_not_moved (List.mem_toFinset.mpr member))]

/-- Equal parent maps identify the root without comparing depth witnesses. -/
theorem HeapView.root_eq_of_parent_eq {n : ℕ} (first second : HeapView n)
    (parents : first.parent = second.parent) : first.root = second.root := by
  apply second.parent_eq_none
  rw [← parents]
  exact first.root_parent

/-- Parent equality determines every non-root side by external order. Only
the root's unused administrative side needs a separate equality. -/
theorem HeapView.side_eq_of_parent_eq {n : ℕ} (first second : HeapView n)
    (parents : first.parent = second.parent)
    (rootSides : first.side first.root = second.side second.root) : first.side = second.side := by
  funext element
  cases parent : first.parent element with
  | none =>
      have atRoot := first.parent_eq_none element parent
      rw [atRoot, first.root_eq_of_parent_eq second parents]
      simpa only [first.root_eq_of_parent_eq second parents] using rootSides
  | some owner =>
      have firstOrder := first.side_order parent
      have secondParent : second.parent element = some owner := by rw [← parents]; exact parent
      have secondOrder := second.side_order secondParent
      cases firstSide : first.side element <;> cases secondSide : second.side element <;>
        simp only [firstSide, secondSide] at firstOrder secondOrder ⊢ <;> first | rfl | omega

end Splay.Lazy
