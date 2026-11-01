import TangoSquared.Paper20261030.SourceProgramObservation

/-! The counted spine kernels in the actual leaf-oriented source language.
The only runtime register is a natural countdown. All source subtrees below
are ghost representation data; the executable controller uses adjacent moves
and rotations only. The existing GapBST compiler can compile these routines.
-/

namespace DynamicOptimality.SingleFinger.SourceSpine

open TangoSquared.Paper20261030 ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

abbrev Cell (α ρ : Type*) := ρ × Source α ρ

abbrev node (left : Source α ρ) (record : ρ) (right : Source α ρ) : Source α ρ :=
  .fork record left right

def rightSpine (gap : Source α ρ) : List (Cell α ρ) → Source α ρ
  | [] => gap
  | (entry, nextGap)::cells => node gap entry (rightSpine nextGap cells)

def leftSpine (gap : Source α ρ) : List (Cell α ρ) → Source α ρ
  | [] => gap
  | (entry, nextGap)::cells => leftSpine (node gap entry nextGap) cells

@[simp] theorem rightSpine_nil (gap : Source α ρ) : rightSpine gap [] = gap := rfl
@[simp] theorem leftSpine_nil (gap : Source α ρ) : leftSpine gap [] = gap := rfl

theorem leftSpine_append (gap : Source α ρ) (first last : List (Cell α ρ)) :
    leftSpine gap (first++last) = leftSpine (leftSpine gap first) last := by
  induction first generalizing gap with
  | nil => rfl
  | cons cell cells ih => exact ih (node gap cell.1 cell.2)

/-- The only runtime information used by a counted rotation kernel. -/
def rotations (action : Move) : Program Nat ρ
  | 0 => .halt
  | count+1 => .nav action count

/-- Expose the selected cell by left rotations. Every hanging subtree is
preserved in its inorder gap. `offset` leaves room for a caller continuation. -/
theorem expose_left (gap : Source α ρ)
    (front : List (Cell α ρ))
    (pivot : ρ) (afterGap : Source α ρ)
    (back : List (Cell α ρ))
    (outside : List (Frame α ρ)) (offset : Nat) :
    Steps (rotations .rotateLeft) (front.length+offset)
      ⟨rightSpine gap (front++(pivot,afterGap)::back),outside⟩ offset
      ⟨node (leftSpine gap front) pivot (rightSpine afterGap back),outside⟩ [] front.length := by
  induction front generalizing gap with
  | nil => simpa only [List.length_nil,List.nil_append,Nat.zero_add,rightSpine,leftSpine] using
      (Steps.nil (program := rotations _) offset ⟨node gap pivot (rightSpine afterGap back),outside⟩)
  | cons cell front ih =>
    rcases cell with ⟨entry,nextGap⟩
    have moved : navigate .rotateLeft
        (Cursor.mk (rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back)) outside) =
        some ⟨rightSpine (node gap entry nextGap) (front++(pivot,afterGap)::back),outside⟩ := by
      cases front with
      | nil => rfl
      | cons cell front => cases cell; rfl
    have first : Step (rotations .rotateLeft) (front.length+offset+1)
        ⟨rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back),outside⟩ (front.length+offset)
        ⟨rightSpine (node gap entry nextGap) (front++(pivot,afterGap)::back),outside⟩ none :=
      .nav rfl moved
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,leftSpine,Option.toList_none,List.nil_append] using
      Steps.next first (ih (node gap entry nextGap))

/-- Inverse of `expose_left`, again as actual local rotations. -/
theorem expose_right (gap : Source α ρ)
    (front : List (Cell α ρ))
    (pivot : ρ) (afterGap : Source α ρ)
    (back : List (Cell α ρ))
    (outside : List (Frame α ρ)) (offset : Nat) :
    Steps (rotations .rotateRight) (front.length+offset)
      ⟨node (leftSpine gap front) pivot (rightSpine afterGap back),outside⟩ offset
      ⟨rightSpine gap (front++(pivot,afterGap)::back),outside⟩ [] front.length := by
  induction front generalizing gap offset with
  | nil => simpa only [List.length_nil,List.nil_append,Nat.zero_add,rightSpine,leftSpine] using
      (Steps.nil (program := rotations _) offset ⟨node gap pivot (rightSpine afterGap back),outside⟩)
  | cons cell front ih =>
    rcases cell with ⟨entry,nextGap⟩
    have moved : navigate .rotateRight
        (Cursor.mk (rightSpine (node gap entry nextGap) (front++(pivot,afterGap)::back)) outside) =
        some ⟨rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back),outside⟩ := by
      cases front with
      | nil => rfl
      | cons cell front => cases cell; rfl
    have last : Step (rotations .rotateRight) (offset+1)
        ⟨rightSpine (node gap entry nextGap) (front++(pivot,afterGap)::back),outside⟩ offset
        ⟨rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back),outside⟩ none :=
      .nav rfl moved
    have run := (ih (node gap entry nextGap) (offset+1)).append last.prefix
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,leftSpine,
      List.nil_append,Option.toList_none] using run

/-- Convert a nonempty right spine to a left spine in exactly one fewer
rotation than the number of its cells. -/
theorem turn_left (gap : Source α ρ)
    (cells : List (Cell α ρ))
    (pivot : ρ) (afterGap : Source α ρ)
    (outside : List (Frame α ρ)) (offset : Nat) :
    Steps (rotations .rotateLeft) (cells.length+offset)
      ⟨rightSpine gap (cells++[(pivot,afterGap)]),outside⟩ offset
      ⟨leftSpine gap (cells++[(pivot,afterGap)]),outside⟩ [] cells.length := by
  simpa only [leftSpine_append,leftSpine,rightSpine] using
    expose_left gap cells pivot afterGap [] outside offset

theorem turn_right (gap : Source α ρ)
    (cells : List (Cell α ρ))
    (pivot : ρ) (afterGap : Source α ρ)
    (outside : List (Frame α ρ)) (offset : Nat) :
    Steps (rotations .rotateRight) (cells.length+offset)
      ⟨leftSpine gap (cells++[(pivot,afterGap)]),outside⟩ offset
      ⟨rightSpine gap (cells++[(pivot,afterGap)]),outside⟩ [] cells.length := by
  simpa only [leftSpine_append,leftSpine,rightSpine] using
    expose_right gap cells pivot afterGap [] outside offset

end DynamicOptimality.SingleFinger.SourceSpine
