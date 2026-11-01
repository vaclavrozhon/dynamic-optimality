import Splay.Lazy.OrderedChildren

namespace Splay.Lazy.HeapView

/-- Reparent a finite set of children to one common owner. This is the
simultaneous heap operation used when entire shrinking intervals transfer. -/
noncomputable def reparentSet {n : ℕ} (view : HeapView n)
    (owner : Element n) (side : Side) (moved : Finset (Element n))
    (ordered : view.HeapOrdered) (notRoot : view.root ∉ moved)
    (ranks : ∀ element ∈ moved, view.rank owner < view.rank element)
    (sideOrder : ∀ element ∈ moved, match side with
      | .left => element.val < owner.val | .right => owner.val < element.val) : HeapView n where
  rank := view.rank
  root := view.root
  parent := fun element => if element ∈ moved then some owner else view.parent element
  side := fun element => if element ∈ moved then side else view.side element
  topDown := orderedChildren
    (fun element => if element ∈ moved then some owner else view.parent element)
    (fun element => if element ∈ moved then side else view.side element)
  level := view.rank
  root_parent := by simp [notRoot, view.root_parent]
  parent_eq_none := by
    intro element absent
    by_cases selected : element ∈ moved
    · simp [selected] at absent
    · simp only [selected, ↓reduceIte] at absent
      exact view.parent_eq_none element absent
  parent_level_lt := by
    intro element parent found
    by_cases selected : element ∈ moved
    · simp only [selected, ↓reduceIte, Option.some.injEq] at found
      subst parent
      exact ranks element selected
    · simp only [selected, ↓reduceIte] at found
      exact ordered found
  side_order := by
    intro element parent found
    by_cases selected : element ∈ moved
    · simp only [selected, ↓reduceIte, Option.some.injEq] at found
      subst parent
      simp only [selected, ↓reduceIte]
      exact sideOrder element selected
    · simp only [selected, ↓reduceIte] at found ⊢
      exact view.side_order found
  topDown_nodup := orderedChildren_nodup _ _
  topDown_ordered := orderedChildren_ordered _ _
  mem_topDown_iff := by intros; exact mem_orderedChildren_iff _ _

theorem reparentSet_heapOrdered {n : ℕ} (view : HeapView n)
    (owner : Element n) (side : Side) (moved : Finset (Element n))
    (ordered : view.HeapOrdered) (notRoot : view.root ∉ moved)
    (ranks : ∀ element ∈ moved, view.rank owner < view.rank element)
    (sideOrder) :
    (view.reparentSet owner side moved ordered notRoot ranks sideOrder).HeapOrdered := by
  intro element parent found
  exact (view.reparentSet owner side moved ordered notRoot ranks sideOrder).parent_level_lt found

@[simp]
theorem reparentSet_parent {n : ℕ} (view : HeapView n)
    (owner : Element n) (side : Side) (moved : Finset (Element n))
    (ordered : view.HeapOrdered) (notRoot : view.root ∉ moved) (ranks) (sideOrder)
    (element : Element n) :
    (view.reparentSet owner side moved ordered notRoot ranks sideOrder).parent element =
      if element ∈ moved then some owner else view.parent element := rfl

@[simp]
theorem reparentSet_side {n : ℕ} (view : HeapView n)
    (owner : Element n) (side : Side) (moved : Finset (Element n))
    (ordered : view.HeapOrdered) (notRoot : view.root ∉ moved) (ranks) (sideOrder)
    (element : Element n) :
    (view.reparentSet owner side moved ordered notRoot ranks sideOrder).side element =
      if element ∈ moved then side else view.side element := rfl

@[simp]
theorem reparentSet_rank {n : ℕ} (view : HeapView n)
    (owner : Element n) (side : Side) (moved : Finset (Element n))
    (ordered : view.HeapOrdered) (notRoot : view.root ∉ moved) (ranks) (sideOrder) :
    (view.reparentSet owner side moved ordered notRoot ranks sideOrder).rank = view.rank := rfl

@[simp]
theorem reparentSet_root {n : ℕ} (view : HeapView n)
    (owner : Element n) (side : Side) (moved : Finset (Element n))
    (ordered : view.HeapOrdered) (notRoot : view.root ∉ moved) (ranks) (sideOrder) :
    (view.reparentSet owner side moved ordered notRoot ranks sideOrder).root = view.root := rfl

end Splay.Lazy.HeapView
