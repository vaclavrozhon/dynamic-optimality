import Splay.Lazy.OrderedChildren
import Splay.Lazy.Canonical

namespace Splay.Lazy.HeapView

/-- The local heap transformation of a heavy-path junction: promote a child,
demote its former owner, and move a selected set of the owner's other children
to the promoted vertex. Numeric ranks are deliberately independent. -/
def promotionParent {n : ℕ} (view : HeapView n) (owner promoted : Element n)
    (moved : Finset (Element n)) (element : Element n) : Option (Element n) :=
  if element = owner then some promoted else
  if element = promoted then view.parent owner else
  if element ∈ moved then some promoted else view.parent element

/-- Doubling the old topological levels leaves room for the reversed edge.
This avoids assuming heap order of the transient numeric priorities. -/
def promotionLevel {n : ℕ} (view : HeapView n) (owner promoted : Element n) (element : Element n) : ℕ :=
  if element = promoted then 2 * view.level owner else
  if element = owner then 2 * view.level owner + 1 else 2 * view.level element

theorem promotionParent_level_lt {n : ℕ} (view : HeapView n) (owner promoted : Element n)
    (moved : Finset (Element n)) (edge : view.parent promoted = some owner)
    (children : ∀ element ∈ moved, view.parent element = some owner)
    {element parent : Element n} (attached : view.promotionParent owner promoted moved element = some parent) :
    view.promotionLevel owner promoted parent < view.promotionLevel owner promoted element := by
  have levels := view.parent_level_lt edge
  have different : owner ≠ promoted := by intro equal; rw [equal] at levels; omega
  by_cases atOwner : element = owner
  · subst element
    simp only [promotionParent, ↓reduceIte, Option.some.injEq] at attached
    subst parent
    simp [promotionLevel, different, different.symm]
  · by_cases atPromoted : element = promoted
    · subst element
      simp only [promotionParent, different.symm, ↓reduceIte] at attached
      have parentLevel := view.parent_level_lt attached
      have parentNeOwner : parent ≠ owner := by intro equal; rw [equal] at parentLevel; omega
      have parentNePromoted : parent ≠ promoted := by intro equal; rw [equal] at parentLevel; omega
      simp only [promotionLevel, parentNePromoted, parentNeOwner, ↓reduceIte]
      omega
    · by_cases selected : element ∈ moved
      · simp only [promotionParent, atOwner, atPromoted, selected, ↓reduceIte, Option.some.injEq] at attached
        subst parent
        have childLevel := view.parent_level_lt (children element selected)
        simp only [promotionLevel, atPromoted, atOwner, ↓reduceIte]
        omega
      · simp only [promotionParent, atOwner, atPromoted, selected, ↓reduceIte] at attached
        have childLevel := view.parent_level_lt attached
        by_cases parentPromoted : parent = promoted
        · subst parent
          simp only [promotionLevel, atPromoted, atOwner, ↓reduceIte]
          omega
        · by_cases parentOwner : parent = owner
          · subst parent
            simp only [promotionLevel, different, atPromoted, atOwner, ↓reduceIte]
            omega
          · simp only [promotionLevel, parentPromoted, parentOwner, atPromoted, atOwner, ↓reduceIte]
            omega

/-- A concrete transient heap view for a single child promotion, including
its checked acyclic parent structure and both sorted child orders. -/
noncomputable def promoteChild {n : ℕ} (view : HeapView n) (owner promoted : Element n)
    (moved : Finset (Element n)) (edge : view.parent promoted = some owner)
    (children : ∀ element ∈ moved, view.parent element = some owner) : HeapView n := by
  classical
  have levels := view.parent_level_lt edge
  have different : owner ≠ promoted := by intro equal; rw [equal] at levels; omega
  have promotedNotRoot : promoted ≠ view.root := by intro equal; rw [equal, view.root_parent] at edge; contradiction
  have rootNotMoved : view.root ∉ moved := by
    intro member
    have impossible := children _ member
    rw [view.root_parent] at impossible
    contradiction
  let parent := view.promotionParent owner promoted moved
  let side := fun element => match parent element with
    | none => Side.left
    | some ancestor => Splay.Lazy.Canonical.sideOf ancestor element
  exact {
    rank := view.rank
    root := if owner = view.root then promoted else view.root
    parent := parent
    side := side
    topDown := orderedChildren parent side
    level := view.promotionLevel owner promoted
    root_parent := by
      by_cases ownerRoot : owner = view.root
      · simp [parent, promotionParent, ownerRoot, promotedNotRoot, view.root_parent]
      · simp [parent, promotionParent, ownerRoot, Ne.symm ownerRoot, promotedNotRoot.symm, rootNotMoved, view.root_parent]
    parent_eq_none := by
      intro element absent
      by_cases atOwner : element = owner
      · simp [parent, promotionParent, atOwner] at absent
      · by_cases atPromoted : element = promoted
        · have ownerRoot : owner = view.root := by
            apply view.parent_eq_none
            simpa [parent, promotionParent, atPromoted, different.symm] using absent
          simp [ownerRoot, atPromoted]
        · by_cases selected : element ∈ moved
          · simp [parent, promotionParent, atOwner, atPromoted, selected] at absent
          · have oldAbsent : view.parent element = none := by
              simpa [parent, promotionParent, atOwner, atPromoted, selected] using absent
            have elementRoot := view.parent_eq_none element oldAbsent
            have ownerNotRoot : owner ≠ view.root := by intro equal; exact atOwner (elementRoot.trans equal.symm)
            simp [ownerNotRoot, elementRoot]
    parent_level_lt := view.promotionParent_level_lt owner promoted moved edge children
    side_order := by
      intro element ancestor attached
      have levelLt := view.promotionParent_level_lt owner promoted moved edge children attached
      have distinct : ancestor ≠ element := by intro equal; rw [equal] at levelLt; omega
      have order := Splay.Lazy.Canonical.sideOf_order_of_ne distinct
      cases newSide : Splay.Lazy.Canonical.sideOf ancestor element <;>
        simpa only [side, attached, newSide] using order
    topDown_nodup := orderedChildren_nodup parent side
    topDown_ordered := orderedChildren_ordered parent side
    mem_topDown_iff := by intros; exact mem_orderedChildren_iff parent side
  }

@[simp]
theorem promoteChild_parent {n : ℕ} (view : HeapView n) (owner promoted : Element n)
    (moved : Finset (Element n)) (edge : view.parent promoted = some owner)
    (children : ∀ element ∈ moved, view.parent element = some owner) :
    (view.promoteChild owner promoted moved edge children).parent = view.promotionParent owner promoted moved := rfl

@[simp]
theorem promoteChild_rank {n : ℕ} (view : HeapView n) (owner promoted : Element n)
    (moved : Finset (Element n)) (edge : view.parent promoted = some owner)
    (children : ∀ element ∈ moved, view.parent element = some owner) :
    (view.promoteChild owner promoted moved edge children).rank = view.rank := rfl

end Splay.Lazy.HeapView
