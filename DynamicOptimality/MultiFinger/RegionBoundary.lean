import DynamicOptimality.MultiFinger.RegionStep

/-! A prefix or suffix operation touches only the first or last opaque
gap of the retained interior. All interior markers and other physical
gaps belong to the unchanged region frame. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation

variable {α : Type*}

theorem prefix_region (before after : MarkedTree α → MarkedTree α)
    (oldKeys newKeys : List α) (oldHoles newHoles : List (RawTree α))
    (beforeWord : ∀ inner, (before inner).skeleton.inorder = oldKeys++inner.skeleton.inorder)
    (afterWord : ∀ inner, (after inner).skeleton.inorder = newKeys++inner.skeleton.inorder)
    (beforeHoles : ∀ inner, (before inner).holes = oldHoles++inner.holes)
    (afterHoles : ∀ inner, (after inner).holes = newHoles++inner.holes)
    (inside : MarkedTree α) {count : Nat}
    (oldSize : (before (.hole (firstHole inside))).skeleton.size ≤ 3)
    (newSize : (after (.hole (firstHole inside))).skeleton.size ≤ 3)
    (actual : Rotations (before (.hole (firstHole inside))).erase
      (after (.hole (firstHole inside))).erase count) :
    RegionStep (before inside) (after inside) count := by
  let frame : RegionFrame α := {
    beforeKeys := [], beforeHoles := [], beforeCount := rfl
    afterKeys := inside.skeleton.inorder
    afterHoles := inside.holes.tail
    afterCount := firstHole_length inside }
  refine ⟨frame,before (.hole (firstHole inside)),after (.hole (firstHole inside)),
    ?_,?_,oldSize,newSize,actual⟩
  · constructor
    · simp only [frame,beforeWord,MarkedTree.skeleton,Tree.inorder,List.nil_append,List.append_nil]
    · simp only [frame,beforeHoles,MarkedTree.holes,List.nil_append,List.append_assoc,List.singleton_append]
      rw [← firstHole_holes]
  · constructor
    · simp only [frame,afterWord,MarkedTree.skeleton,Tree.inorder,List.nil_append,List.append_nil]
    · simp only [frame,afterHoles,MarkedTree.holes,List.nil_append,List.append_assoc,List.singleton_append]
      rw [← firstHole_holes]

theorem suffix_region (before after : MarkedTree α → MarkedTree α)
    (oldKeys newKeys : List α) (oldHoles newHoles : List (RawTree α))
    (beforeWord : ∀ inner, (before inner).skeleton.inorder = inner.skeleton.inorder++oldKeys)
    (afterWord : ∀ inner, (after inner).skeleton.inorder = inner.skeleton.inorder++newKeys)
    (beforeHoles : ∀ inner, (before inner).holes = inner.holes++oldHoles)
    (afterHoles : ∀ inner, (after inner).holes = inner.holes++newHoles)
    (inside : MarkedTree α) {count : Nat}
    (oldSize : (before (.hole (lastHole inside))).skeleton.size ≤ 3)
    (newSize : (after (.hole (lastHole inside))).skeleton.size ≤ 3)
    (actual : Rotations (before (.hole (lastHole inside))).erase
      (after (.hole (lastHole inside))).erase count) :
    RegionStep (before inside) (after inside) count := by
  let frame : RegionFrame α := {
    beforeKeys := inside.skeleton.inorder
    beforeHoles := inside.holes.dropLast
    beforeCount := lastHole_length inside
    afterKeys := [], afterHoles := [], afterCount := rfl }
  refine ⟨frame,before (.hole (lastHole inside)),after (.hole (lastHole inside)),
    ?_,?_,oldSize,newSize,actual⟩
  · constructor
    · simp only [frame,beforeWord,MarkedTree.skeleton,Tree.inorder,List.nil_append,List.append_nil]
    · simp only [frame,beforeHoles,MarkedTree.holes,List.append_nil]
      rw [← List.append_assoc,← lastHole_holes]
  · constructor
    · simp only [frame,afterWord,MarkedTree.skeleton,Tree.inorder,List.nil_append,List.append_nil]
    · simp only [frame,afterHoles,MarkedTree.holes,List.append_nil]
      rw [← List.append_assoc,← lastHole_holes]

end DynamicOptimality.MultiFinger
