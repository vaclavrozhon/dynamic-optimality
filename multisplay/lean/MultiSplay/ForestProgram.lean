import MultiSplay.ForestDomains
import MultiSplay.RawRotation

/-!
# Primitive comparator programs on changing domains

A program consists of rotations, root services, common root splits and joins.
A rotation at depth `d` has charge `d + 1`; the other primitives have charge one.
This charge bounds their ordinary pointer cost up to a universal constant.
-/

namespace MultiSplay.CommonForest

open DynamicOptimality (RawTree)
open TangoSquared.MTR.Tree (inorder)

variable {α : Type*}

inductive RootAccess : Access α
  | root (left : RawTree α) (key : α) (right : RawTree α) :
      RootAccess key (.node left key right) (.node left key right) 0

def RotationPreparation : Preparation α := fun a b cost =>
  ∃ depth, Rotation depth a b ∧ cost = depth + 1

abbrev Program := @Trace α RootAccess RotationPreparation

/-- Changing execution relations does not alter events, endpoints, or cost. -/
theorem Step.mapRelations {access access' : Access α} {prepare prepare' : Preparation α}
    (accessMap : ∀ {key a b work}, access key a b work → access' key a b work)
    (prepareMap : ∀ {a b work}, prepare a b work → prepare' a b work)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (step : Step access prepare a word b work) : Step access' prepare' a word b work := by
  induction step with
  | search execution => exact .search (accessMap execution)
  | split execution => exact .split (accessMap execution)
  | join => exact .join _ _ _
  | prepare execution => exact .prepare (prepareMap execution)
  | context step front back ih => exact .context ih front back
  | reorder order => exact .reorder order

theorem Trace.mapRelations {access access' : Access α} {prepare prepare' : Preparation α}
    (accessMap : ∀ {key a b work}, access key a b work → access' key a b work)
    (prepareMap : ∀ {a b work}, prepare a b work → prepare' a b work)
    {a b : List (RawTree α)} {word : List (Event α)} {work : Nat}
    (run : Trace access prepare a word b work) : Trace access' prepare' a word b work := by
  induction run with
  | nil => exact .nil _
  | cons step rest ih => exact .cons (step.mapRelations accessMap prepareMap) ih

theorem rootAccess_preserves : AccessPreserves (RootAccess : Access α) := by
  intro key a b cost execution
  cases execution
  rfl

end MultiSplay.CommonForest
