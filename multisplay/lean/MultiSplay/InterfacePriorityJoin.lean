import MultiSplay.InterfaceRootOperations

/-!
# Exact interface join for doubled true priorities

Each new edge has contracted value three. The ordinary join first attaches
both old roots at value two; two further paid unit increases synchronize the
values. There are eight primitive operations, two insertions, four increases,
and no pairing activity. Every pre-existing block remains literally intact.
-/

namespace MultiSplay.InterfaceForest

open Splay.Interface

variable {n : Nat}

def priorityJoin (state : State n) (pivot left right : Element n) : State n :=
  setValue (setValue (join state pivot left right) left 3) right 3

def priorityJoinWord (state : State n) (pivot left right : Element n) : List (Operation n) :=
  joinWord state pivot left right ++ [.valueChange left .increase, .valueChange right .increase]

theorem priorityJoin_trace {params : Parameters} (state : State n) (pivot left right : Element n)
    (valid : state.Valid params) (leftNe : left ≠ pivot) (rightNe : right ≠ pivot)
    (childrenNe : right ≠ left) (valueCap : 3 ≤ params.valueBound)
    (pivotOne : state.value pivot = 1) (leftOne : state.value left = 1) (rightOne : state.value right = 1)
    (leftFree : left ∉ state.allElements) (rightFree : right ∉ state.allElements)
    (room : state.growingCount pivot + 2 ≤ params.growingLimit) :
    Trace params state (priorityJoinWord state pivot left right) (priorityJoin state pivot left right) := by
  have joined := join_trace state pivot left right valid leftNe rightNe childrenNe
    pivotOne leftOne rightOne leftFree rightFree room
  have joinedValid := trace_final_valid joined
  have leftTwo : (join state pivot left right).value left = 2 := by
    simp [join, attach, appendBlock, setValue, childrenNe.symm]
  have rightTwo : (setValue (join state pivot left right) left 3).value right = 2 := by
    simp [join, attach, appendBlock, setValue, childrenNe]
  have first : Step params (join state pivot left right) (.valueChange left .increase)
      (setValue (join state pivot left right) left 3) := by
    simpa only [leftTwo] using increase_step _ left joinedValid (by rw [leftTwo]; omega)
  have second : Step params (setValue (join state pivot left right) left 3) (.valueChange right .increase)
      (priorityJoin state pivot left right) := by
    simpa only [rightTwo, priorityJoin] using increase_step _ right first.2.2 (by rw [rightTwo]; omega)
  exact trace_append joined (.cons first (.cons second (.nil second.2.2)))

theorem priorityJoin_blocks (state : State n) (pivot left right : Element n) :
    (priorityJoin state pivot left right).blocks =
      state.blocks ++ [rootBlock pivot [left], rootBlock pivot [right]] := join_blocks _ _ _ _

theorem priorityJoin_left_value (state : State n) (pivot left right : Element n) (different : right ≠ left) :
    (priorityJoin state pivot left right).value left = 3 := by simp [priorityJoin, setValue, different.symm]

theorem priorityJoin_right_value (state : State n) (pivot left right : Element n) :
    (priorityJoin state pivot left right).value right = 3 := by simp [priorityJoin, setValue]

theorem priorityJoin_other_value (state : State n) (pivot left right element : Element n)
    (notLeft : element ≠ left) (notRight : element ≠ right) :
    (priorityJoin state pivot left right).value element = state.value element := by
  simp [priorityJoin, join, attach, appendBlock, setValue, notLeft, notRight]

@[simp] theorem priorityJoinWord_inserts (state : State n) (pivot left right : Element n) :
    totalInserts (priorityJoinWord state pivot left right) = 2 := by simp [priorityJoinWord]; rfl

@[simp] theorem priorityJoinWord_increases (state : State n) (pivot left right : Element n) :
    totalIncreases (priorityJoinWord state pivot left right) = 4 := by simp [priorityJoinWord]; rfl

@[simp] theorem priorityJoinWord_activity (state : State n) (pivot left right : Element n) :
    totalActivity (priorityJoinWord state pivot left right) = 0 := by simp [priorityJoinWord]; rfl

end MultiSplay.InterfaceForest
