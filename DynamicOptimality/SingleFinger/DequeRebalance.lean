import DynamicOptimality.SingleFinger.Counted

/-! Linear rebuilding of a deque in the actual one-pointer BST model.

A nonempty deque consists of a pivot, an increasing right spine on its left,
and a decreasing left spine on its right. Its minimum and maximum cells are
therefore at distance at most one from the pivot. Arbitrary hanging subtrees
remain in their inorder gaps. Every routine is the same counted local program
`Counted.code`, with at most a constant number of counted blocks.
-/

namespace DynamicOptimality.SingleFinger.Deque

open TangoSquared.MTR TangoSquared.Paper20261030.Auxiliary LocalProgram
open Spine Counted

variable {κ α ρ : Type*}

abbrev Entry (α ρ : Type*) := NodeRecord α (fun _ => ρ)

private theorem leftSpine_nonempty (gap : RawTree κ) (cells : List (Cell κ))
    (nonempty : gap ≠ .empty) : leftSpine gap cells ≠ .empty := by
  induction cells generalizing gap with
  | nil => exact nonempty
  | cons cell cells ih => exact ih _ (by simp)

private theorem leftSpine_has_cell (gap : RawTree κ) {cells : List (Cell κ)}
    (nonempty : cells ≠ []) : leftSpine gap cells ≠ .empty := by
  cases cells with
  | nil => exact False.elim (nonempty rfl)
  | cons cell cells => exact leftSpine_nonempty _ cells (by simp)

private theorem rightSpine_has_cell (gap : RawTree κ) {cells : List (Cell κ)}
    (nonempty : cells ≠ []) : rightSpine gap cells ≠ .empty := by
  cases cells with
  | nil => exact False.elim (nonempty rfl)
  | cons cell cells => cases cell; simp [rightSpine]

private theorem down_left {left right : RawTree κ} {entry : κ} {outside}
    (nonempty : left ≠ .empty) :
    navigate .left ⟨.node left entry right,outside⟩ = some ⟨left,.left entry right::outside⟩ := by
  cases left with
  | empty => exact False.elim (nonempty rfl)
  | node => rfl

private theorem down_right {left right : RawTree κ} {entry : κ} {outside}
    (nonempty : right ≠ .empty) :
    navigate .right ⟨.node left entry right,outside⟩ = some ⟨right,.right left entry::outside⟩ := by
  cases right with
  | empty => exact False.elim (nonempty rfl)
  | node => rfl

/-- Empty spines need no rotation; nonempty spines need `length - 1`. -/
theorem turn_left_all (gap : RawTree (Entry α ρ)) (cells : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (prepend .rotateLeft (cells.length-1) rest) ⟨rightSpine gap cells,outside⟩
      rest ⟨leftSpine gap cells,outside⟩ [] (cells.length-1) := by
  induction cells using List.reverseRecOn with
  | nil => exact .nil _ _
  | append_singleton cells cell ih =>
    rcases cell with ⟨entry,afterGap⟩
    simpa only [List.length_append,List.length_singleton,Nat.add_sub_cancel,Nat.add_zero] using
      Counted.lift (Spine.turn_left gap cells entry afterGap outside 0) rest

theorem turn_right_all (gap : RawTree (Entry α ρ)) (cells : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (prepend .rotateRight (cells.length-1) rest) ⟨leftSpine gap cells,outside⟩
      rest ⟨rightSpine gap cells,outside⟩ [] (cells.length-1) := by
  induction cells using List.reverseRecOn with
  | nil => exact .nil _ _
  | append_singleton cells cell ih =>
    rcases cell with ⟨entry,afterGap⟩
    simpa only [List.length_append,List.length_singleton,Nat.add_sub_cancel,Nat.add_zero] using
      Counted.lift (Spine.turn_right gap cells entry afterGap outside 0) rest

def sidePlan (side action : Move) (count : Nat) (rest : Schedule) : Schedule :=
  if count = 0 then rest else
    prepend side 1 (prepend action (count-1) (prepend .up 1 rest))

def sideCost (count : Nat) : Nat := if count = 0 then 0 else count+1

theorem sideCost_bound (count : Nat) : sideCost count ≤ count+1 := by
  unfold sideCost
  split <;> omega

theorem left_to_right (gap : RawTree (Entry α ρ)) (cells : List (Cell (Entry α ρ)))
    (pivot : Entry α ρ) (right : RawTree (Entry α ρ))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (sidePlan .left .rotateRight cells.length rest)
      ⟨.node (leftSpine gap cells) pivot right,outside⟩ rest
      ⟨.node (rightSpine gap cells) pivot right,outside⟩ [] (sideCost cells.length) := by
  by_cases empty : cells = []
  · subst cells
    exact .nil _ _
  · have positive : cells.length ≠ 0 := by simpa using empty
    have body := turn_right_all gap cells (.left pivot right::outside) (prepend .up 1 rest)
    have first := Counted.one (down_left (right := right) (entry := pivot) (outside := outside) (leftSpine_has_cell gap empty))
      (prepend .rotateRight (cells.length-1) (prepend .up 1 rest))
    have last := Counted.one (α := α) (ρ := ρ)
      (before := ⟨rightSpine gap cells,.left pivot right::outside⟩)
      (action := .up) rfl rest
    have run := first.append (body.append last)
    simpa only [sidePlan,sideCost,if_neg positive,List.nil_append,
      show 1+(cells.length-1+1) = cells.length+1 by omega] using run

theorem left_to_left (gap : RawTree (Entry α ρ)) (cells : List (Cell (Entry α ρ)))
    (pivot : Entry α ρ) (right : RawTree (Entry α ρ))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (sidePlan .left .rotateLeft cells.length rest)
      ⟨.node (rightSpine gap cells) pivot right,outside⟩ rest
      ⟨.node (leftSpine gap cells) pivot right,outside⟩ [] (sideCost cells.length) := by
  by_cases empty : cells = []
  · subst cells
    exact .nil _ _
  · have positive : cells.length ≠ 0 := by simpa using empty
    have body := turn_left_all gap cells (.left pivot right::outside) (prepend .up 1 rest)
    have first := Counted.one (down_left (right := right) (entry := pivot) (outside := outside) (rightSpine_has_cell gap empty))
      (prepend .rotateLeft (cells.length-1) (prepend .up 1 rest))
    have last := Counted.one (α := α) (ρ := ρ)
      (before := ⟨leftSpine gap cells,.left pivot right::outside⟩)
      (action := .up) rfl rest
    have run := first.append (body.append last)
    simpa only [sidePlan,sideCost,if_neg positive,List.nil_append,
      show 1+(cells.length-1+1) = cells.length+1 by omega] using run

theorem right_to_left (left : RawTree (Entry α ρ)) (pivot : Entry α ρ)
    (gap : RawTree (Entry α ρ)) (cells : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (sidePlan .right .rotateLeft cells.length rest)
      ⟨.node left pivot (rightSpine gap cells),outside⟩ rest
      ⟨.node left pivot (leftSpine gap cells),outside⟩ [] (sideCost cells.length) := by
  by_cases empty : cells = []
  · subst cells
    exact .nil _ _
  · have positive : cells.length ≠ 0 := by simpa using empty
    have body := turn_left_all gap cells (.right left pivot::outside) (prepend .up 1 rest)
    have first := Counted.one (down_right (left := left) (entry := pivot) (outside := outside) (rightSpine_has_cell gap empty))
      (prepend .rotateLeft (cells.length-1) (prepend .up 1 rest))
    have last := Counted.one (α := α) (ρ := ρ)
      (before := ⟨leftSpine gap cells,.right left pivot::outside⟩)
      (action := .up) rfl rest
    have run := first.append (body.append last)
    simpa only [sidePlan,sideCost,if_neg positive,List.nil_append,
      show 1+(cells.length-1+1) = cells.length+1 by omega] using run

theorem right_to_right (left : RawTree (Entry α ρ)) (pivot : Entry α ρ)
    (gap : RawTree (Entry α ρ)) (cells : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (sidePlan .right .rotateRight cells.length rest)
      ⟨.node left pivot (leftSpine gap cells),outside⟩ rest
      ⟨.node left pivot (rightSpine gap cells),outside⟩ [] (sideCost cells.length) := by
  by_cases empty : cells = []
  · subst cells
    exact .nil _ _
  · have positive : cells.length ≠ 0 := by simpa using empty
    have body := turn_right_all gap cells (.right left pivot::outside) (prepend .up 1 rest)
    have first := Counted.one (down_right (left := left) (entry := pivot) (outside := outside) (leftSpine_has_cell gap empty))
      (prepend .rotateRight (cells.length-1) (prepend .up 1 rest))
    have last := Counted.one (α := α) (ρ := ρ)
      (before := ⟨rightSpine gap cells,.right left pivot::outside⟩)
      (action := .up) rfl rest
    have run := first.append (body.append last)
    simpa only [sidePlan,sideCost,if_neg positive,List.nil_append,
      show 1+(cells.length-1+1) = cells.length+1 by omega] using run

/-- The schedule for arranging a right spine around a selected pivot. -/
def assemblePlan (front back : Nat) (rest : Schedule) : Schedule :=
  prepend .rotateLeft front
    (sidePlan .left .rotateRight front (sidePlan .right .rotateLeft back rest))

def assembleCost (front back : Nat) : Nat := front + sideCost front + sideCost back

theorem assemble (gap : RawTree (Entry α ρ)) (front : List (Cell (Entry α ρ)))
    (pivot : Entry α ρ) (afterGap : RawTree (Entry α ρ)) (back : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (assemblePlan front.length back.length rest)
      ⟨rightSpine gap (front++(pivot,afterGap)::back),outside⟩ rest
      ⟨.node (rightSpine gap front) pivot (leftSpine afterGap back),outside⟩ []
      (assembleCost front.length back.length) := by
  have first := Counted.lift (expose_left gap front pivot afterGap back outside 0)
    (sidePlan .left .rotateRight front.length (sidePlan .right .rotateLeft back.length rest))
  have middle := left_to_right gap front pivot (rightSpine afterGap back) outside
    (sidePlan .right .rotateLeft back.length rest)
  have last := right_to_left (rightSpine gap front) pivot afterGap back outside rest
  simpa only [assemblePlan,assembleCost,Nat.add_zero,List.nil_append,Nat.add_assoc] using
    first.append (middle.append last)

def flattenPlan (front back : Nat) (rest : Schedule) : Schedule :=
  sidePlan .left .rotateLeft front
    (sidePlan .right .rotateRight back (prepend .rotateRight front rest))

def flattenCost (front back : Nat) : Nat := sideCost front + sideCost back + front

theorem flatten (gap : RawTree (Entry α ρ)) (front : List (Cell (Entry α ρ)))
    (pivot : Entry α ρ) (afterGap : RawTree (Entry α ρ)) (back : List (Cell (Entry α ρ)))
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (flattenPlan front.length back.length rest)
      ⟨.node (rightSpine gap front) pivot (leftSpine afterGap back),outside⟩ rest
      ⟨rightSpine gap (front++(pivot,afterGap)::back),outside⟩ []
      (flattenCost front.length back.length) := by
  have first := left_to_left gap front pivot (leftSpine afterGap back) outside
    (sidePlan .right .rotateRight back.length (prepend .rotateRight front.length rest))
  have middle := right_to_right (leftSpine gap front) pivot afterGap back outside
    (prepend .rotateRight front.length rest)
  have last := Counted.lift (expose_right gap front pivot afterGap back outside 0) rest
  simpa only [flattenPlan,flattenCost,Nat.add_zero,List.nil_append,Nat.add_assoc] using
    first.append (middle.append last)

/-- Rebuilding uses a fixed-size schedule, determined solely by four lengths. -/
def rebuildPlan (oldFront oldBack newFront newBack : Nat) (rest : Schedule) : Schedule :=
  flattenPlan oldFront oldBack (assemblePlan newFront newBack rest)

def rebuildCost (oldFront oldBack newFront newBack : Nat) : Nat :=
  flattenCost oldFront oldBack + assembleCost newFront newBack

/-- A concrete legal rebuilding theorem, including all untouched subtrees.
The equality of cell lists is a representation fact, never controller input. -/
theorem rebuild (gap : RawTree (Entry α ρ))
    (oldFront : List (Cell (Entry α ρ))) (oldPivot : Entry α ρ)
    (oldAfter : RawTree (Entry α ρ)) (oldBack : List (Cell (Entry α ρ)))
    (newFront : List (Cell (Entry α ρ))) (newPivot : Entry α ρ)
    (newAfter : RawTree (Entry α ρ)) (newBack : List (Cell (Entry α ρ)))
    (same : oldFront++(oldPivot,oldAfter)::oldBack = newFront++(newPivot,newAfter)::newBack)
    (outside : List (Pointer.Frame (Entry α ρ))) (rest : Schedule) :
    Steps code (rebuildPlan oldFront.length oldBack.length newFront.length newBack.length rest)
      ⟨.node (rightSpine gap oldFront) oldPivot (leftSpine oldAfter oldBack),outside⟩ rest
      ⟨.node (rightSpine gap newFront) newPivot (leftSpine newAfter newBack),outside⟩ []
      (rebuildCost oldFront.length oldBack.length newFront.length newBack.length) := by
  have first := flatten gap oldFront oldPivot oldAfter oldBack outside
    (assemblePlan newFront.length newBack.length rest)
  rw [same] at first
  simpa only [rebuildPlan,rebuildCost,List.nil_append] using first.append
    (assemble gap newFront newPivot newAfter newBack outside rest)

theorem rebuildCost_bound {oldFront oldBack newFront newBack : Nat}
    (sameSize : oldFront+oldBack = newFront+newBack) :
    rebuildCost oldFront oldBack newFront newBack ≤ 4*(oldFront+oldBack)+4 := by
  have a := sideCost_bound oldFront
  have b := sideCost_bound oldBack
  have c := sideCost_bound newFront
  have d := sideCost_bound newBack
  unfold rebuildCost flattenCost assembleCost
  omega

end DynamicOptimality.SingleFinger.Deque
