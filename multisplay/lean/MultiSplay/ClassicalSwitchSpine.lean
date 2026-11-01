import MultiSplay.ClassicalSwitchExecution

/-!
# Nearest reference-ancestor guards from a preferred-path spine

Entries are `(edge, ancestor key)`, with the innermost ancestor first.
The edge is false for a left child and true for a right child. The spine is
interpreted through the existing pointer frames, with empty off-path children.
The first right-edge entry is exactly the lower guard; the first left-edge
entry is exactly the upper guard. Farther ancestors remain in the corresponding
outside domain. No auxiliary tree shape participates in this calculation.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder)
open TangoSquared.MTR.Pointer (Frame)

variable {α : Type*}

abbrev Spine (α : Type*) := List (Bool × α)

namespace Spine

def frame (entry : Bool × α) : Frame α :=
  if entry.1 then .right .empty entry.2 else .left entry.2 .empty

def plug (spine : Spine α) (focus : RawTree α) : RawTree α :=
  TangoSquared.MTR.Pointer.plug focus (spine.map frame)

def lowerKeys : Spine α → List α
  | [] => []
  | (false,_) :: above => lowerKeys above
  | (true,key) :: above => lowerKeys above ++ [key]

def upperKeys : Spine α → List α
  | [] => []
  | (false,key) :: above => key :: upperKeys above
  | (true,_) :: above => upperKeys above

def lower : Spine α → Boundary α
  | [] => .absent
  | (false,_) :: above => lower above
  | (true,key) :: above => .guard (lowerKeys above) key

def upper : Spine α → Boundary α
  | [] => .absent
  | (false,key) :: above => .guard (upperKeys above) key
  | (true,_) :: above => upper above

@[simp] theorem lower_domain (spine : Spine α) : spine.lower.lowerKeys = spine.lowerKeys := by
  induction spine with
  | nil => rfl
  | cons entry above ih => cases entry with
    | mk side key => cases side with
      | false => exact ih
      | true => rfl

@[simp] theorem upper_domain (spine : Spine α) : spine.upper.upperKeys = spine.upperKeys := by
  induction spine with
  | nil => rfl
  | cons entry above ih => cases entry with
    | mk side key => cases side with
      | false => rfl
      | true => exact ih

@[simp] theorem plug_nil (focus : RawTree α) : plug [] focus = focus := rfl

@[simp] theorem plug_left (key : α) (above : Spine α) (focus : RawTree α) :
    plug ((false,key)::above) focus = plug above (.node focus key .empty) := rfl

@[simp] theorem plug_right (key : α) (above : Spine α) (focus : RawTree α) :
    plug ((true,key)::above) focus = plug above (.node .empty key focus) := rfl

theorem plug_append (inside outside : Spine α) (focus : RawTree α) :
    plug (inside ++ outside) focus = plug outside (plug inside focus) := by
  induction inside generalizing focus with
  | nil => rfl
  | cons entry above ih => cases entry with
    | mk side key => cases side <;> simp only [List.cons_append, plug_left, plug_right, ih]

theorem inorder_plug (spine : Spine α) (focus : RawTree α) :
    inorder (spine.plug focus) = spine.lowerKeys ++ inorder focus ++ spine.upperKeys := by
  induction spine generalizing focus with
  | nil => simp [lowerKeys, upperKeys]
  | cons entry above ih => cases entry with
    | mk side key => cases side <;>
        simp [plug_left, plug_right, lowerKeys, upperKeys, ih, inorder, List.append_assoc]

def before (oldSide : Bool) (spine : Spine α) (old : RawTree α) (pivot : α) : RawTree α :=
  spine.plug (if oldSide then .node .empty pivot old else .node old pivot .empty)

@[simp] theorem before_inorder (oldSide : Bool) (spine : Spine α) (old : RawTree α) (pivot : α) :
    inorder (before oldSide spine old pivot) =
      beforeKeys oldSide spine.lower spine.upper (inorder old) pivot := by
  cases oldSide <;> simp [before, inorder_plug, beforeKeys, inorder, List.append_assoc]

/-- Guards and event domains are now calculated from the reference ancestors.
Only equality of the current auxiliary's inorder domain is needed to transfer
this geometry to its arbitrary actual shape. -/
theorem execution_exists (oldSide : Bool) (spine : Spine α) (old incoming whole : RawTree α)
    (pivot : α) (keys : inorder whole = inorder (before oldSide spine old pivot))
    (unique : (inorder whole).Nodup) :
    ∃ after parked rotations,
      Execution pivot incoming oldSide spine.lower spine.upper whole after parked rotations ∧
      inorder parked = inorder old :=
  ClassicalSwitch.execution_exists oldSide spine.lower spine.upper (inorder old) incoming whole pivot
    (keys.trans (before_inorder oldSide spine old pivot)) unique

end Spine
end MultiSplay.ClassicalSwitch
