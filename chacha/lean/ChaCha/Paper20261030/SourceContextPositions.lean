import ChaCha.Paper20261030.SourceRotationPositions

/-! Lifting a local change of finger addresses through an unchanged
outside context. Addresses outside the changed subtree are untouched.
This gives the stationary-finger rule for a rotation at arbitrary depth.
-/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer

variable {α ρ : Type*}

def underChild (right : Bool) (change : List Bool → List Bool) : List Bool → List Bool
  | [] => []
  | first::rest => first::(if first = right then change rest else rest)

def underContext : List (Frame α ρ) → (List Bool → List Bool) → List Bool → List Bool
  | [],change => change
  | first::rest,change => underContext rest (underChild (direction first) change)

theorem left_context_record {before after : Source α ρ} (record : ρ) (sibling : Source α ρ)
    (change : List Bool → List Bool)
    (preserved : ∀ position, recordAt after (change position) = recordAt before position) (position : List Bool) :
    recordAt (.fork record after sibling) (underChild false change position) =
      recordAt (.fork record before sibling) position := by
  cases position with
  | nil => rfl
  | cons first rest => cases first with
    | false => exact preserved rest
    | true => rfl

theorem right_context_record {before after : Source α ρ} (record : ρ) (sibling : Source α ρ)
    (change : List Bool → List Bool)
    (preserved : ∀ position, recordAt after (change position) = recordAt before position) (position : List Bool) :
    recordAt (.fork record sibling after) (underChild true change position) =
      recordAt (.fork record sibling before) position := by
  cases position with
  | nil => rfl
  | cons first rest => cases first with
    | false => rfl
    | true => exact preserved rest

theorem context_record {before after : Source α ρ} (outside : List (Frame α ρ))
    (change : List Bool → List Bool)
    (preserved : ∀ position, recordAt after (change position) = recordAt before position) (position : List Bool) :
    recordAt (plug after outside) (underContext outside change position) = recordAt (plug before outside) position := by
  induction outside generalizing before after change with
  | nil => exact preserved position
  | cons frame rest ih => cases frame with
    | left record sibling =>
      exact ih (underChild false change) (left_context_record record sibling change preserved)
    | right sibling record =>
      exact ih (underChild true change) (right_context_record record sibling change preserved)

theorem context_right_valid (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (position : List Bool) (current : Cursor α ρ)
    (reached : locate (plug (.fork top (.fork p u v) w) outside) position = some current) :
    ∃ target, locate (plug (.fork p u (.fork top v w)) outside) (underContext outside rightAddress position) = some target ∧
      target.focus.rootRecord = current.focus.rootRecord := by
  apply valid_of_record
  rw [context_record outside rightAddress (rotate_right_record u v w p top),← locate_record,reached]
  rfl

theorem context_left_valid (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (position : List Bool) (current : Cursor α ρ)
    (reached : locate (plug (.fork p u (.fork top v w)) outside) position = some current) :
    ∃ target, locate (plug (.fork top (.fork p u v) w) outside) (underContext outside leftAddress position) = some target ∧
      target.focus.rootRecord = current.focus.rootRecord := by
  apply valid_of_record
  rw [context_record outside leftAddress (rotate_left_record u v w p top),← locate_record,reached]
  rfl

end ChaCha.Paper20261030.SourcePositions
