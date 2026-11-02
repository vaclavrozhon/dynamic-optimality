import DynamicOptimality.LocalProgramComposition

/-!
# Executable spine kernels for the single-finger simulator

The intended compiler has five layers: counted local rotations; double-ended
queues represented by two opposite spines; a tendon represented by two such
queues; a bounded marked skeleton joining the source fingers; and instruction
simulation from `MultiSourceProgram` to `LocalProgram.Steps`. The simulator's
potential must be the persistent sum of the queue imbalances. Final telescoping
must preserve leaf-service events and must cover copy and absent fingers.

This module implements the first layer. A cell consists of a key record and
the subtree immediately following that key in inorder. These subtrees are
arbitrary: the controller neither inspects them nor stores them in registers.
`rightSpine gap cells` links the cells increasingly; `leftSpine gap cells`
links the same cells decreasingly. The initial subtree `gap` precedes all
cells. All tree-valued arguments occur only in the representation and proofs.
The executing program stores only a move and a natural countdown.

The later layers, and hence the general multifinger simulation theorem, are
not asserted by this module.
-/

namespace DynamicOptimality.SingleFinger.Spine

open ChaCha.MTR ChaCha.Paper20261030.Auxiliary LocalProgram

variable {κ α ρ : Type*}

/-- A key record together with the unchanged subtree following it. -/
abbrev Cell (κ : Type*) := κ × RawTree κ

def rightSpine (gap : RawTree κ) : List (Cell κ) → RawTree κ
  | [] => gap
  | (entry, nextGap)::cells => .node gap entry (rightSpine nextGap cells)

def leftSpine (gap : RawTree κ) : List (Cell κ) → RawTree κ
  | [] => gap
  | (entry, nextGap)::cells => leftSpine (.node gap entry nextGap) cells

@[simp] theorem rightSpine_nil (gap : RawTree κ) : rightSpine gap [] = gap := rfl
@[simp] theorem leftSpine_nil (gap : RawTree κ) : leftSpine gap [] = gap := rfl

theorem leftSpine_append (gap : RawTree κ) (first last : List (Cell κ)) :
    leftSpine gap (first++last) = leftSpine (leftSpine gap first) last := by
  induction first generalizing gap with
  | nil => rfl
  | cons cell cells ih => exact ih (.node gap cell.1 cell.2)

theorem rightSpine_inorder (gap : RawTree κ) (cells : List (Cell κ)) :
    (rightSpine gap cells).inorder = gap.inorder ++
      cells.flatMap (fun cell => [cell.1]++cell.2.inorder) := by
  induction cells generalizing gap with
  | nil => simp [rightSpine]
  | cons cell cells ih =>
    rcases cell with ⟨entry,nextGap⟩
    simp [rightSpine,Tree.inorder,ih,List.append_assoc]

theorem leftSpine_inorder (gap : RawTree κ) (cells : List (Cell κ)) :
    (leftSpine gap cells).inorder = gap.inorder ++
      cells.flatMap (fun cell => [cell.1]++cell.2.inorder) := by
  induction cells generalizing gap with
  | nil => simp [leftSpine]
  | cons cell cells ih =>
    rcases cell with ⟨entry,nextGap⟩
    simp [leftSpine,Tree.inorder,ih,List.append_assoc]

theorem inorder_eq (gap : RawTree κ) (cells : List (Cell κ)) :
    (leftSpine gap cells).inorder = (rightSpine gap cells).inorder := by
  rw [leftSpine_inorder,rightSpine_inorder]

/-- The only runtime information used by a counted rotation kernel. -/
def rotations (action : Move) : Program Nat α ρ
  | 0 => .halt
  | count+1 => .nav action count

/-- Expose the selected cell by left rotations. Every hanging subtree is
preserved in its inorder gap. `offset` leaves room for a caller continuation. -/
theorem expose_left (gap : RawTree (NodeRecord α (fun _ => ρ)))
    (front : List (Cell (NodeRecord α (fun _ => ρ))))
    (pivot : NodeRecord α (fun _ => ρ)) (afterGap : RawTree (NodeRecord α (fun _ => ρ)))
    (back : List (Cell (NodeRecord α (fun _ => ρ))))
    (outside : List (Pointer.Frame (NodeRecord α (fun _ => ρ)))) (offset : Nat) :
    Steps (rotations .rotateLeft) (front.length+offset)
      ⟨rightSpine gap (front++(pivot,afterGap)::back),outside⟩ offset
      ⟨.node (leftSpine gap front) pivot (rightSpine afterGap back),outside⟩ [] front.length := by
  induction front generalizing gap with
  | nil => simpa only [List.length_nil,List.nil_append,Nat.zero_add,rightSpine,leftSpine] using
      (Steps.nil (program := rotations _) offset ⟨.node gap pivot (rightSpine afterGap back),outside⟩)
  | cons cell front ih =>
    rcases cell with ⟨entry,nextGap⟩
    have moved : navigate .rotateLeft
        (Pointer.Cursor.mk (rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back)) outside) =
        some ⟨rightSpine (.node gap entry nextGap) (front++(pivot,afterGap)::back),outside⟩ := by
      cases front with
      | nil => rfl
      | cons cell front => cases cell; rfl
    have first : Step (rotations .rotateLeft) (front.length+offset+1)
        ⟨rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back),outside⟩ (front.length+offset)
        ⟨rightSpine (.node gap entry nextGap) (front++(pivot,afterGap)::back),outside⟩ none :=
      .nav rfl moved
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,leftSpine,Option.toList_none,List.nil_append] using
      Steps.next first (ih (.node gap entry nextGap))

/-- Inverse of `expose_left`, again as actual local rotations. -/
theorem expose_right (gap : RawTree (NodeRecord α (fun _ => ρ)))
    (front : List (Cell (NodeRecord α (fun _ => ρ))))
    (pivot : NodeRecord α (fun _ => ρ)) (afterGap : RawTree (NodeRecord α (fun _ => ρ)))
    (back : List (Cell (NodeRecord α (fun _ => ρ))))
    (outside : List (Pointer.Frame (NodeRecord α (fun _ => ρ)))) (offset : Nat) :
    Steps (rotations .rotateRight) (front.length+offset)
      ⟨.node (leftSpine gap front) pivot (rightSpine afterGap back),outside⟩ offset
      ⟨rightSpine gap (front++(pivot,afterGap)::back),outside⟩ [] front.length := by
  induction front generalizing gap offset with
  | nil => simpa only [List.length_nil,List.nil_append,Nat.zero_add,rightSpine,leftSpine] using
      (Steps.nil (program := rotations _) offset ⟨.node gap pivot (rightSpine afterGap back),outside⟩)
  | cons cell front ih =>
    rcases cell with ⟨entry,nextGap⟩
    have moved : navigate .rotateRight
        (Pointer.Cursor.mk (rightSpine (.node gap entry nextGap) (front++(pivot,afterGap)::back)) outside) =
        some ⟨rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back),outside⟩ := by
      cases front with
      | nil => rfl
      | cons cell front => cases cell; rfl
    have last : Step (rotations .rotateRight) (offset+1)
        ⟨rightSpine (.node gap entry nextGap) (front++(pivot,afterGap)::back),outside⟩ offset
        ⟨rightSpine gap ((entry,nextGap)::front++(pivot,afterGap)::back),outside⟩ none :=
      .nav rfl moved
    have run := (ih (.node gap entry nextGap) (offset+1)).append last.prefix
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,leftSpine,
      List.nil_append,Option.toList_none] using run

/-- Convert a nonempty right spine to a left spine in exactly one fewer
rotation than the number of its cells. -/
theorem turn_left (gap : RawTree (NodeRecord α (fun _ => ρ)))
    (cells : List (Cell (NodeRecord α (fun _ => ρ))))
    (pivot : NodeRecord α (fun _ => ρ)) (afterGap : RawTree (NodeRecord α (fun _ => ρ)))
    (outside : List (Pointer.Frame (NodeRecord α (fun _ => ρ)))) (offset : Nat) :
    Steps (rotations .rotateLeft) (cells.length+offset)
      ⟨rightSpine gap (cells++[(pivot,afterGap)]),outside⟩ offset
      ⟨leftSpine gap (cells++[(pivot,afterGap)]),outside⟩ [] cells.length := by
  simpa only [leftSpine_append,leftSpine,rightSpine] using
    expose_left gap cells pivot afterGap [] outside offset

theorem turn_right (gap : RawTree (NodeRecord α (fun _ => ρ)))
    (cells : List (Cell (NodeRecord α (fun _ => ρ))))
    (pivot : NodeRecord α (fun _ => ρ)) (afterGap : RawTree (NodeRecord α (fun _ => ρ)))
    (outside : List (Pointer.Frame (NodeRecord α (fun _ => ρ)))) (offset : Nat) :
    Steps (rotations .rotateRight) (cells.length+offset)
      ⟨leftSpine gap (cells++[(pivot,afterGap)]),outside⟩ offset
      ⟨rightSpine gap (cells++[(pivot,afterGap)]),outside⟩ [] cells.length := by
  simpa only [leftSpine_append,leftSpine,rightSpine] using
    expose_right gap cells pivot afterGap [] outside offset

end DynamicOptimality.SingleFinger.Spine
