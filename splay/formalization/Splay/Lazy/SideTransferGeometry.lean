import Splay.Lazy.ReparentSet
import Mathlib.Data.List.Sort

namespace Splay.Lazy

/-- Before a whole-side transfer the boundary is the bottommost child.
The transferred prefix lies above all old children of the boundary. -/
structure SideTransferGeometry {n : ℕ} (before : HeapView n)
    (source boundary : Element n) (side : Side) where
  moved : List (Element n)
  decomposition : before.topDown source side = moved ++ [boundary]
  ranks : ∀ element ∈ moved, before.rank boundary < before.rank element
  outermost : ∀ element ∈ moved, ∀ child ∈ before.topDown boundary side,
    if side = .left then element.val < child.val else child.val < element.val

namespace SideTransferGeometry

variable {n : ℕ} {before : HeapView n} {source boundary : Element n} {side : Side}
  (geometry : SideTransferGeometry before source boundary side)

/-- Every selected element has the old common source and side. -/
theorem moved_parent_side {element : Element n} (member : element ∈ geometry.moved) :
    before.parent element = some source ∧ before.side element = side := by
  apply before.mem_topDown_iff.mp
  rw [geometry.decomposition]
  exact List.mem_append_left _ member

include geometry in
theorem boundary_parent_side : before.parent boundary = some source ∧ before.side boundary = side := by
  apply before.mem_topDown_iff.mp
  rw [geometry.decomposition]
  simp

include geometry in
theorem source_ne_boundary : source ≠ boundary := by
  intro equal
  have strict := before.parent_level_lt geometry.boundary_parent_side.1
  rw [equal] at strict
  exact Nat.lt_irrefl _ strict

theorem moved_nodup : geometry.moved.Nodup := by
  have distinct := before.topDown_nodup source side
  rw [geometry.decomposition] at distinct
  exact (List.nodup_append.mp distinct).1

theorem boundary_not_moved : boundary ∉ geometry.moved := by
  have distinct := before.topDown_nodup source side
  rw [geometry.decomposition] at distinct
  intro member
  exact (List.nodup_append.mp distinct).2.2 boundary member boundary (by simp) rfl

theorem root_not_moved : before.root ∉ geometry.moved.toFinset := by
  intro member
  have parent := (geometry.moved_parent_side (List.mem_toFinset.mp member)).1
  rw [before.root_parent] at parent
  contradiction

theorem sideOrder : ∀ element ∈ geometry.moved.toFinset,
    if side = .left then element.val < boundary.val else boundary.val < element.val := by
  intro element member
  have inside := List.mem_toFinset.mp member
  cases side with
  | left =>
      have ordered := (before.topDown_ordered source).1
      rw [geometry.decomposition] at ordered
      exact (List.pairwise_append.mp ordered).2.2 element inside boundary (by simp)
  | right =>
      have ordered := (before.topDown_ordered source).2
      rw [geometry.decomposition] at ordered
      exact (List.pairwise_append.mp ordered).2.2 element inside boundary (by simp)

/-- The simultaneous heap endpoint is constructed from the transferred prefix. -/
noncomputable def after (ordered : before.HeapOrdered) : HeapView n :=
  before.reparentSet boundary side geometry.moved.toFinset ordered geometry.root_not_moved
    (fun element member => geometry.ranks element (List.mem_toFinset.mp member))
    (by intro element member; cases side <;> simpa using geometry.sideOrder element member)

theorem after_ordered (ordered : before.HeapOrdered) : (geometry.after ordered).HeapOrdered :=
  before.reparentSet_heapOrdered _ _ _ _ _ _ _

@[simp]
theorem after_parent (ordered : before.HeapOrdered) (element : Element n) :
    (geometry.after ordered).parent element = if element ∈ geometry.moved then some boundary else before.parent element := by
  simp [after]

@[simp]
theorem after_side (ordered : before.HeapOrdered) (element : Element n) :
    (geometry.after ordered).side element = if element ∈ geometry.moved then side else before.side element := by
  simp [after]

theorem source_topDown (ordered : before.HeapOrdered) :
    (geometry.after ordered).topDown source side = [boundary] := by
  have membership : ∀ element, element ∈ (geometry.after ordered).topDown source side ↔ element ∈ [boundary] := by
    intro element
    by_cases selected : element ∈ geometry.moved
    · simp [HeapView.mem_topDown_iff, geometry.after_parent, geometry.after_side, selected,
        geometry.source_ne_boundary.symm,
        show element ≠ boundary from fun equal => geometry.boundary_not_moved (equal ▸ selected)]
    · rw [(geometry.after ordered).mem_topDown_iff, geometry.after_parent, geometry.after_side,
        if_neg selected, if_neg selected, ← before.mem_topDown_iff, geometry.decomposition]
      simp [selected]
  cases side with
  | left => exact List.Pairwise.eq_of_mem_iff ((geometry.after ordered).topDown_ordered source).1 (by simp) membership
  | right => exact List.Pairwise.eq_of_mem_iff ((geometry.after ordered).topDown_ordered source).2 (by simp) membership

/-- The transferred intervals precede every old interval of their new owner. -/
theorem boundary_topDown (ordered : before.HeapOrdered) :
    (geometry.after ordered).topDown boundary side = geometry.moved ++ before.topDown boundary side := by
  have membership : ∀ element, element ∈ (geometry.after ordered).topDown boundary side ↔
      element ∈ geometry.moved ++ before.topDown boundary side := by
    intro element
    by_cases selected : element ∈ geometry.moved
    · simp [HeapView.mem_topDown_iff, geometry.after_parent, geometry.after_side, selected]
    · rw [(geometry.after ordered).mem_topDown_iff, geometry.after_parent, geometry.after_side,
        if_neg selected, if_neg selected, ← before.mem_topDown_iff]
      simp [selected]
  cases side with
  | left =>
      have oldOrder := (before.topDown_ordered source).1
      rw [geometry.decomposition] at oldOrder
      apply List.Pairwise.eq_of_mem_iff ((geometry.after ordered).topDown_ordered boundary).1 _ membership
      exact List.pairwise_append.mpr ⟨(List.pairwise_append.mp oldOrder).1,
        (before.topDown_ordered boundary).1, by simpa using geometry.outermost⟩
  | right =>
      have oldOrder := (before.topDown_ordered source).2
      rw [geometry.decomposition] at oldOrder
      apply List.Pairwise.eq_of_mem_iff ((geometry.after ordered).topDown_ordered boundary).2 _ membership
      exact List.pairwise_append.mpr ⟨(List.pairwise_append.mp oldOrder).1,
        (before.topDown_ordered boundary).2, by simpa using geometry.outermost⟩

/-- Every unrelated owner-side placement keeps exactly its previous child list. -/
theorem other_topDown (ordered : before.HeapOrdered) (owner : Element n) (childSide : Side)
    (notSource : owner ≠ source ∨ childSide ≠ side)
    (notBoundary : owner ≠ boundary ∨ childSide ≠ side) :
    (geometry.after ordered).topDown owner childSide = before.topDown owner childSide := by
  have membership : ∀ element, element ∈ (geometry.after ordered).topDown owner childSide ↔
      element ∈ before.topDown owner childSide := by
    intro element
    by_cases selected : element ∈ geometry.moved
    · have old := geometry.moved_parent_side selected
      simp only [HeapView.mem_topDown_iff, geometry.after_parent, geometry.after_side, selected,
        ↓reduceIte, old.1, old.2, Option.some.injEq]
      constructor
      · rintro ⟨equalOwner, equalSide⟩
        rcases notBoundary with different | different
        · exact False.elim (different equalOwner.symm)
        · exact False.elim (different equalSide.symm)
      · rintro ⟨equalOwner, equalSide⟩
        rcases notSource with different | different
        · exact False.elim (different equalOwner.symm)
        · exact False.elim (different equalSide.symm)
    · simp [HeapView.mem_topDown_iff, geometry.after_parent, geometry.after_side, selected]
  cases childSide with
  | left =>
      exact List.Pairwise.eq_of_mem_iff ((geometry.after ordered).topDown_ordered owner).1
        (before.topDown_ordered owner).1 membership
  | right =>
      exact List.Pairwise.eq_of_mem_iff ((geometry.after ordered).topDown_ordered owner).2
        (before.topDown_ordered owner).2 membership

end SideTransferGeometry
end Splay.Lazy
