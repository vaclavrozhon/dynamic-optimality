import DynamicOptimality.SearchRotationModel

/-!
# Literal subtree ports at deque ends

A port is a tree context with its hole one or two edges below the root.
Its other subtrees are arbitrary and stay untouched. Both substitution and
exposure below are statements about ordinary rotations on the original keys.
-/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

variable {α : Type*}

structure LeftPort (α : Type*) where
  pivot : α
  right : RawTree α
  middle : Option (α × RawTree α)

structure RightPort (α : Type*) where
  left : RawTree α
  pivot : α
  middle : Option (RawTree α × α)

def LeftPort.fill (port : LeftPort α) (gap : RawTree α) : RawTree α :=
  match port.middle with
  | none => .node gap port.pivot port.right
  | some (key, inside) => .node (.node gap key inside) port.pivot port.right

def RightPort.fill (port : RightPort α) (gap : RawTree α) : RawTree α :=
  match port.middle with
  | none => .node port.left port.pivot gap
  | some (inside, key) => .node port.left port.pivot (.node inside key gap)

theorem LeftPort.lift (port : LeftPort α) {before after : RawTree α} {count : Nat}
    (run : Rotations before after count) : Rotations (port.fill before) (port.fill after) count := by
  cases port with
  | mk pivot right middle =>
      cases middle with
      | none => exact run.plug [.left pivot right]
      | some data => exact run.plug [.left data.1 data.2, .left pivot right]

theorem RightPort.lift (port : RightPort α) {before after : RawTree α} {count : Nat}
    (run : Rotations before after count) : Rotations (port.fill before) (port.fill after) count := by
  cases port with
  | mk left pivot middle =>
      cases middle with
      | none => exact run.plug [.right left pivot]
      | some data => exact run.plug [.right data.1 data.2, .right left pivot]

theorem LeftPort.extract (port : LeftPort α) (left right : RawTree α) (key : α) :
    ∃ count ≤ 2, Rotations (port.fill (.node left key right))
      (.node left key (port.fill right)) count := by
  cases port with
  | mk pivot outside middle =>
      cases middle with
      | none => exact ⟨1, by omega, .singleton (.rootRight _ _ _ _ _)⟩
      | some data =>
          exact ⟨2, le_rfl, .step (.leftContext (.rootRight _ _ _ _ _) _ _)
            (.singleton (.rootRight _ _ _ _ _))⟩

theorem RightPort.extract (port : RightPort α) (left right : RawTree α) (key : α) :
    ∃ count ≤ 2, Rotations (port.fill (.node left key right))
      (.node (port.fill left) key right) count := by
  cases port with
  | mk outside pivot middle =>
      cases middle with
      | none => exact ⟨1, by omega, .singleton (.rootLeft _ _ _ _ _)⟩
      | some data =>
          exact ⟨2, le_rfl, .step (.rightContext _ _ (.rootLeft _ _ _ _ _))
            (.singleton (.rootLeft _ _ _ _ _))⟩

end DynamicOptimality.GeometricOnlineSimulation
