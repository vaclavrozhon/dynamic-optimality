import DynamicOptimality.SingleFinger.SourceSpine

/-! Fixed-size schedules of counted adjacent moves and rotations. A schedule
contains no addresses or source-tree representation. In the deque kernels its
length is bounded by a constant, while its counters store spine lengths. -/

namespace DynamicOptimality.SingleFinger.SourceCounted

open TangoSquared.Paper20261030 SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

abbrev Schedule := List (Move × Nat)

def prepend (action : Move) : Nat → Schedule → Schedule
  | 0, rest => rest
  | count+1, rest => (action,count+1)::rest

def code : Program Schedule ρ
  | [] => .halt
  | (_,0)::rest => code rest
  | (action,count+1)::rest => .nav action (prepend action count rest)

theorem embed (action : Move) (rest : Schedule) (count : Nat)
    (active : SourceSpine.rotations (ρ := ρ) action count ≠ .halt) :
    code (ρ := ρ) (prepend action count rest) =
      (SourceSpine.rotations action count).mapState (fun n => prepend action n rest) := by
  cases count with
  | zero => exact False.elim (active rfl)
  | succ count => rfl

theorem lift {action : Move} {count cost : Nat}
    {before after : Cursor α ρ}
    (steps : Steps (SourceSpine.rotations action) count before 0 after [] cost) (rest : Schedule) :
    Steps code (prepend action count rest) before rest after [] cost := by
  exact (steps.run rfl).map_prefix (fun n => prepend action n rest) (embed action rest)

theorem one {action : Move} {before after : Cursor α ρ}
    (moved : navigate action before = some after) (rest : Schedule) :
    Steps code (prepend action 1 rest) before rest after [] 1 := by
  exact (Step.nav (program := code) (state := prepend action 1 rest) rfl moved).prefix

end DynamicOptimality.SingleFinger.SourceCounted
