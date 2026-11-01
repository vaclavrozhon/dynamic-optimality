import Splay.Accounting.CanonicalJunctionParentCells
import Splay.Accounting.FullOrderSegment

namespace Splay.Lazy.IsSegment

/-- A segment of an asymmetrically ordered list contains every ambient
element whose order lies between two of its elements. -/
theorem mem_of_rel_between {α : Type*} {R : α → α → Prop} {inside whole : List α}
    (segment : IsSegment inside whole) (ordered : whole.Pairwise R)
    (asymmetric : ∀ {a b}, R a b → ¬ R b a)
    {first middle last : α} (firstIn : first ∈ inside) (lastIn : last ∈ inside)
    (middleIn : middle ∈ whole) (before : R first middle) (after : R middle last) :
    middle ∈ inside := by
  obtain ⟨front, back, decomposition⟩ := segment
  rw [decomposition] at ordered middleIn
  rcases List.mem_append.mp middleIn with early | late
  · rcases List.mem_append.mp early with inFront | inInside
    · have reverse := (List.pairwise_append.mp (List.pairwise_append.mp ordered).1).2.2 middle inFront first firstIn
      exact (asymmetric before reverse).elim
    · exact inInside
  · have reverse := (List.pairwise_append.mp ordered).2.2 last (List.mem_append_right _ lastIn) middle late
    exact (asymmetric after reverse).elim

end Splay.Lazy.IsSegment

namespace Splay.Accounting.JunctionBendReduction

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical

/-- A nonempty ordinary block contained in one relocation cell is a
contiguous block at its actual new parent, with its original side and order.
Both the new parent and segment geometry are derived from canonical edges. -/
theorem exists_canonical_segment_after_of_same_relocationCell {n : ℕ}
    (before after : Snapshot n) (tree : BST 0 n) {owner : External n} {side : Side}
    {elements : List (External n)} (nonempty : elements ≠ [])
    (segment : IsSegment elements ((canonicalHeapView before tree).topDown owner side))
    (ordinary : ∀ element ∈ elements, element ∉ junctionExceptionsFrom before after tree (Nat.le_refl n))
    (sameCell : ∀ first ∈ elements, ∀ second ∈ elements,
      SameCutCell (relocationCutsFrom before after tree (Nat.le_refl n)) first second) :
    ∃ nextOwner, IsSegment elements ((canonicalHeapView after tree).topDown nextOwner side) := by
  classical
  obtain ⟨first, firstIn⟩ := List.exists_mem_of_ne_nil elements nonempty
  have oldParent (element : External n) (inside : element ∈ elements) :
      canonicalParent before tree element = some owner :=
    ((canonicalHeapView before tree).mem_topDown_iff.mp (segment.mem inside)).1
  obtain ⟨firstEdge, firstMember, _, firstChild⟩ := exists_edge_of_canonicalParent before tree (oldParent first firstIn)
  obtain ⟨firstNext, firstNextMember, firstNextChild, _, _, _, _⟩ :=
    exists_edge_same_attachment_side_of_not_mem_exceptions before after tree (Nat.le_refl n) 0 firstMember
      (by simpa only [firstChild] using ordinary first firstIn)
  let nextOwner := firstNext.owner
  have firstNew : canonicalParent after tree first = some nextOwner := by
    have attached := canonicalParent_eq_some_of_mem_fullEdges after tree firstNext firstNextMember
    simpa only [firstNextChild, firstChild] using attached
  have newParent (element : External n) (inside : element ∈ elements) :
      canonicalParent after tree element = some nextOwner := by
    have parentsEq := canonicalParents_eq_of_sameCutCell before after tree (oldParent element inside) (oldParent first firstIn)
      (ordinary element inside) (ordinary first firstIn)
      ((sameCell element inside first firstIn).mono (Finset.subset_union_left))
    exact parentsEq.trans firstNew
  have newMembers : ∀ element ∈ elements,
      element ∈ (canonicalHeapView after tree).topDown nextOwner side := by
    intro element inside
    have oldPlacement := (canonicalHeapView before tree).mem_topDown_iff.mp (segment.mem inside)
    apply (canonicalHeapView after tree).mem_topDown_iff.mpr
    exact ⟨newParent element inside,
      (canonicalSide_eq_of_not_mem_junctionExceptions before after tree oldPlacement.1 (ordinary element inside)).trans oldPlacement.2⟩
  let R := fun a b : External n => match side with
    | .left => a.val < b.val
    | .right => b.val < a.val
  have oldOrder : ((canonicalHeapView before tree).topDown owner side).Pairwise R := by
    cases side with
    | left => exact ((canonicalHeapView before tree).topDown_ordered owner).1
    | right => exact ((canonicalHeapView before tree).topDown_ordered owner).2
  have newOrder : ((canonicalHeapView after tree).topDown nextOwner side).Pairwise R := by
    cases side with
    | left => exact ((canonicalHeapView after tree).topDown_ordered nextOwner).1
    | right => exact ((canonicalHeapView after tree).topDown_ordered nextOwner).2
  have asymmetric : ∀ {a b}, R a b → ¬ R b a := by
    intro a b forward reverse
    cases side <;> change _ < _ at forward reverse <;> omega
  letI : Std.Antisymm R := ⟨fun _ _ forward reverse => (asymmetric forward reverse).elim⟩
  have oldSublist := Splay.Lazy.Canonical.IsSegment.sublist segment
  have elementsOrdered := oldOrder.sublist oldSublist
  have elementsNodup := ((canonicalHeapView before tree).topDown_nodup owner side).sublist oldSublist
  have newSublist : elements.Sublist ((canonicalHeapView after tree).topDown nextOwner side) :=
    List.sublist_of_subperm_of_pairwise (elementsNodup.subperm newMembers) elementsOrdered newOrder
  refine ⟨nextOwner, isSegment_of_sublist_of_convex newSublist
    ((canonicalHeapView after tree).topDown_nodup nextOwner side) ?_⟩
  intro a middle b aIn bIn between
  have firstRelation : R a middle := between.first_before_middle.rel_of_pairwise newOrder
  have lastRelation : R middle b := between.middle_before_last.rel_of_pairwise newOrder
  have numericalBetween : a.val ≤ middle.val ∧ middle.val ≤ b.val ∨ b.val ≤ middle.val ∧ middle.val ≤ a.val := by
    cases side <;> change _ < _ at firstRelation lastRelation <;> omega
  have middleOrdinary := not_mem_exceptions_of_between_same_relocationCell before after tree (Nat.le_refl n)
    (sameCell a aIn b bIn) (ordinary a aIn) (ordinary b bIn) numericalBetween
  have middleCell := (sameCell a aIn b bIn).between numericalBetween
  have middlePlacement := (canonicalHeapView after tree).mem_topDown_iff.mp between.middle_mem
  have inverseParents := canonicalParents_eq_of_sameCutCell after before tree (newParent a aIn) middlePlacement.1
    (by rw [junctionExceptionsFrom_comm after before]; exact ordinary a aIn)
    (by rw [junctionExceptionsFrom_comm after before]; exact middleOrdinary)
    (by
      rw [junctionCutsFrom_comm after before]
      exact middleCell.mono Finset.subset_union_left)
  have middleOldParent : canonicalParent before tree middle = some owner := inverseParents.symm.trans (oldParent a aIn)
  have middleOldSide : canonicalSide before tree middle = side :=
    (canonicalSide_eq_of_not_mem_junctionExceptions before after tree middleOldParent middleOrdinary).symm.trans middlePlacement.2
  have middleOldMember := (canonicalHeapView before tree).mem_topDown_iff.mpr ⟨middleOldParent, middleOldSide⟩
  exact segment.mem_of_rel_between oldOrder asymmetric aIn bIn middleOldMember firstRelation lastRelation

end Splay.Accounting.JunctionBendReduction
