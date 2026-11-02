import ChaCha.Paper20261030.MultiSourceValidity

/-! Local moves and stationary-finger transport commute with putting a
component below an unchanged outside context. These facts support joining
separate component pieces without moving their fingers between pieces.
-/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

theorem address_extend (current : Cursor α ρ) (outside : List (Frame α ρ)) :
    address (current.extend outside) = outside.reverse.map direction ++ address current := by
  simp only [address,Cursor.extend,List.reverse_append,List.map_append]

theorem navigate_extend (action : Move) {before after : Cursor α ρ}
    (moved : navigate action before = some after) (outside : List (Frame α ρ)) :
    navigate action (before.extend outside) = some (after.extend outside) := by
  rcases before with ⟨focus,inside⟩
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases inside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl
  | rotateRight => cases focus with
    | leaf => simp [navigate] at moved
    | fork top l w => cases l with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl

theorem descend_extend {before after : Cursor α ρ} {position : List Bool}
    (reached : descend before position = some after) (outside : List (Frame α ρ)) :
    descend (before.extend outside) position = some (after.extend outside) := by
  induction position generalizing before with
  | nil => cases Option.some.inj reached; rfl
  | cons right rest ih =>
    cases moved : navigate (if right then .right else .left) before with
    | none => simp only [descend,moved,Option.bind_none,reduceCtorEq] at reached
    | some middle =>
      simp only [descend,moved,Option.bind_some] at reached
      simp only [descend,navigate_extend _ moved outside,Option.bind_some]
      exact ih reached

theorem locate_left {tree : Source α ρ} {position : List Bool} {current : Cursor α ρ}
    (reached : locate tree position = some current) (record : ρ) (sibling : Source α ρ) :
    locate (.fork record tree sibling) (false::position) = some (current.extend [.left record sibling]) :=
  descend_extend reached [.left record sibling]

theorem locate_right {tree : Source α ρ} {position : List Bool} {current : Cursor α ρ}
    (reached : locate tree position = some current) (record : ρ) (sibling : Source α ρ) :
    locate (.fork record sibling tree) (true::position) = some (current.extend [.right sibling record]) :=
  descend_extend reached [.right sibling record]

theorem underChild_id (right : Bool) : underChild right id = id := by
  funext position
  cases position with
  | nil => rfl
  | cons first rest => simp [underChild]

theorem underContext_id (outside : List (Frame α ρ)) : underContext outside id = id := by
  induction outside with
  | nil => rfl
  | cons frame rest ih => simp only [underContext,underChild_id,ih]

theorem underContext_append (inside outside : List (Frame α ρ)) (change : List Bool → List Bool) :
    underContext (inside++outside) change = underContext outside (underContext inside change) := by
  induction inside generalizing change with
  | nil => rfl
  | cons frame rest ih => exact ih (underChild (direction frame) change)

end ChaCha.Paper20261030.SourcePositions

namespace ChaCha.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions
open DynamicOptimality.LocalProgram (Move)

variable {α ρ : Type*}

theorem transport_extend (action : Move) (current : Cursor α ρ) (outside : List (Frame α ρ)) :
    transport action (current.extend outside) = underContext outside (transport action current) := by
  cases action <;> simp only [transport,Cursor.extend,underContext_append,underContext_id]

end ChaCha.Paper20261030.MultiSourceProgram
