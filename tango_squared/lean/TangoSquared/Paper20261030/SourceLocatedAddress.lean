import TangoSquared.Paper20261030.SourceCursorPositions

/-! A reached cursor's ghost address is exactly the path used to locate
it. These addresses remain semantic data; local controllers see only the
constant-length direction lists supplied by their finite connector shape.
-/

namespace TangoSquared.Paper20261030.SourcePositions

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

theorem downward_address (right : Bool) (before after : Cursor α ρ)
    (moved : navigate (if right then .right else .left) before = some after) :
    address after = address before++[right] := by
  rcases before with ⟨focus,outside⟩
  cases focus with
  | leaf => cases right <;> simp [navigate] at moved
  | fork record l r =>
    cases right <;> cases Option.some.inj moved <;>
      simp only [address,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,direction]

theorem descend_address (before after : Cursor α ρ) (path : List Bool)
    (reached : descend before path = some after) : address after = address before++path := by
  induction path generalizing before with
  | nil => cases Option.some.inj reached; simp
  | cons right rest ih =>
    cases moved : navigate (if right then .right else .left) before with
    | none => simp only [descend,moved,Option.bind_none,reduceCtorEq] at reached
    | some current =>
      have tail := ih current (by simpa only [descend,moved,Option.bind_some] using reached)
      rw [tail,downward_address right before current moved,List.append_assoc]
      rfl

theorem locate_address (tree : Source α ρ) (path : List Bool) (current : Cursor α ρ)
    (reached : locate tree path = some current) : address current = path := by
  exact descend_address ⟨tree,[]⟩ current path reached

end TangoSquared.Paper20261030.SourcePositions
