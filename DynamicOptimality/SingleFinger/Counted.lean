import DynamicOptimality.SingleFinger.Spine

/-! Fixed-size schedules of counted adjacent moves and rotations. A schedule
contains no addresses or source-tree representation. In the deque kernels its
length is bounded by a constant, while its counters store spine lengths. -/

namespace DynamicOptimality.SingleFinger.Counted

open TangoSquared.MTR TangoSquared.Paper20261030.Auxiliary LocalProgram

variable {α ρ : Type*}

abbrev Schedule := List (Move × Nat)

def prepend (action : Move) : Nat → Schedule → Schedule
  | 0, rest => rest
  | count+1, rest => (action,count+1)::rest

def code : Program Schedule α ρ
  | [] => .halt
  | (_,0)::rest => code rest
  | (action,count+1)::rest => .nav action (prepend action count rest)

theorem embed (action : Move) (rest : Schedule) (count : Nat)
    (active : Spine.rotations (α := α) (ρ := ρ) action count ≠ .halt) :
    code (α := α) (ρ := ρ) (prepend action count rest) =
      (Spine.rotations action count).mapState (fun n => prepend action n rest) := by
  cases count with
  | zero => exact False.elim (active rfl)
  | succ count => rfl

theorem lift {action : Move} {count cost : Nat}
    {before after : Metadata.Cursor α (fun _ => ρ)}
    (steps : Steps (Spine.rotations action) count before 0 after [] cost) (rest : Schedule) :
    Steps code (prepend action count rest) before rest after [] cost := by
  exact (steps.run rfl).map_prefix (fun n => prepend action n rest) (embed action rest)

theorem one {action : Move} {before after : Metadata.Cursor α (fun _ => ρ)}
    (moved : navigate action before = some after) (rest : Schedule) :
    Steps code (prepend action 1 rest) before rest after [] 1 := by
  exact (Step.nav (program := code) (state := prepend action 1 rest) rfl moved).prefix

end DynamicOptimality.SingleFinger.Counted
