import TangoSquared.Paper20261030.GapBSTMetadataTrace
import DynamicOptimality.LocalProgram

/-! Executable local controllers for the appendix's slot-preserving
rotations. Both programs use one physical cursor, eight control phases,
and at most two saved slot records. Their only inputs are charged reads
of the two actual pivot nodes. -/

namespace TangoSquared.Paper20261030.GapBST.Storage

open ColoredStorage DynamicOptimality.LocalProgram

variable {α ρ : Type*}

inductive RotationState (ρ : Type*) where
  | start
  | descend (upper : Slots ρ)
  | readLower (upper : Slots ρ)
  | writeLower (upper lower : Slots ρ)
  | ascend (upper lower : Slots ρ)
  | writeUpper (upper lower : Slots ρ)
  | rotate
  | done

def RotationState.registers : RotationState ρ → List (Slots ρ)
  | .start | .rotate | .done => []
  | .descend upper | .readLower upper => [upper]
  | .writeLower upper lower | .ascend upper lower | .writeUpper upper lower => [upper,lower]

theorem rotation_registers (state : RotationState ρ) : state.registers.length ≤ 2 := by
  cases state <;> simp [RotationState.registers]

def rotationProgram (right : Bool) : Program (RotationState ρ) α (Slots ρ)
  | .start => .read (fun view => .descend view.entry.2.2)
  | .descend upper => .nav (if right then .left else .right) (.readLower upper)
  | .readLower upper => .read (fun view => .writeLower upper view.entry.2.2)
  | .writeLower upper lower =>
      .write (if right then {lower with right := none} else {lower with left := none}) (.ascend upper lower)
  | .ascend upper lower => .nav .up (.writeUpper upper lower)
  | .writeUpper upper lower =>
      .write (if right then {upper with left := lower.right} else {upper with right := lower.left}) .rotate
  | .rotate => .nav (if right then .rotateRight else .rotateLeft) .done
  | .done => .halt

theorem rotate_right_program (u v w : Source α ρ) (p q : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    Run (rotationProgram true) .start (cursor ⟨.fork q (.fork p u v) w,rest⟩)
      .done (cursor ⟨.fork p u (.fork q v w),rest⟩)
      [record (lastKey v) ⟨some q,none,leafRecord w⟩,
       record (lastKey u) ⟨some p,leafRecord u,leafRecord v⟩] 7 := by
  apply Run.next (entry := some (record (lastKey v) ⟨some q,none,leafRecord w⟩)) (cost := 6)
  · apply Step.read (view := ⟨record (lastKey v) ⟨some q,none,leafRecord w⟩,false,empty (gaps w)⟩) <;> rfl
  apply Run.next (entry := none) (cost := 5)
  · apply Step.nav (action := .left) <;> rfl
  apply Run.next (entry := some (record (lastKey u) ⟨some p,leafRecord u,leafRecord v⟩)) (cost := 4)
  · apply Step.read (view := ⟨record (lastKey u) ⟨some p,leafRecord u,leafRecord v⟩,empty (gaps u),empty (gaps v)⟩) <;> rfl
  apply Run.next (entry := none) (cost := 3)
  · apply Step.write; rfl
  apply Run.next (entry := none) (cost := 2)
  · apply Step.nav (action := .up) <;> rfl
  apply Run.next (entry := none) (cost := 1)
  · apply Step.write; rfl
  apply Run.next (entry := none) (cost := 0)
  · apply Step.nav (action := .rotateRight) <;> rfl
  exact Run.halt rfl

theorem rotate_left_program (u v w : Source α ρ) (p q : ρ) (rest : List (SourcePointer.Frame α ρ)) :
    Run (rotationProgram false) .start (cursor ⟨.fork p u (.fork q v w),rest⟩)
      .done (cursor ⟨.fork q (.fork p u v) w,rest⟩)
      [record (lastKey u) ⟨some p,leafRecord u,none⟩,
       record (lastKey v) ⟨some q,leafRecord v,leafRecord w⟩] 7 := by
  apply Run.next (entry := some (record (lastKey u) ⟨some p,leafRecord u,none⟩)) (cost := 6)
  · apply Step.read (view := ⟨record (lastKey u) ⟨some p,leafRecord u,none⟩,empty (gaps u),false⟩) <;> rfl
  apply Run.next (entry := none) (cost := 5)
  · apply Step.nav (action := .right) <;> rfl
  apply Run.next (entry := some (record (lastKey v) ⟨some q,leafRecord v,leafRecord w⟩)) (cost := 4)
  · apply Step.read (view := ⟨record (lastKey v) ⟨some q,leafRecord v,leafRecord w⟩,empty (gaps v),empty (gaps w)⟩) <;> rfl
  apply Run.next (entry := none) (cost := 3)
  · apply Step.write; rfl
  apply Run.next (entry := none) (cost := 2)
  · apply Step.nav (action := .up) <;> rfl
  apply Run.next (entry := none) (cost := 1)
  · apply Step.write; rfl
  apply Run.next (entry := none) (cost := 0)
  · apply Step.nav (action := .rotateLeft) <;> rfl
  exact Run.halt rfl

end TangoSquared.Paper20261030.GapBST.Storage
