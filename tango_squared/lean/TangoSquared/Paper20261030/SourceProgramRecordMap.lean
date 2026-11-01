import TangoSquared.Paper20261030.SourceProgramObservation
import TangoSquared.Paper20261030.SourceRecordMap
import TangoSquared.Paper20261030.SourceRecordInventory

/-! Record erasure commutes with actual cursor navigation. In particular,
a legal move in an erased tree lifts to the same local move in the tree
carrying immutable identifiers. Rotations preserve the record inventory.
-/

namespace TangoSquared.Paper20261030

open ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ τ ι : Type*}

theorem isLeaf_mapRecords (f : ρ → τ) (source : Source α ρ) :
    isLeaf (source.mapRecords f) = isLeaf source := by cases source <;> rfl

theorem navigate_mapRecords (f : ρ → τ) (action : Move) (before : Cursor α ρ) :
    (navigate action before).map (Cursor.mapRecords f) = navigate action (before.mapRecords f) := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | left | right => cases focus <;> rfl
  | up => cases outside with
    | nil => rfl
    | cons frame rest => cases frame <;> rfl
  | rotateRight => cases focus with
    | leaf => rfl
    | fork q l w => cases l <;> rfl
  | rotateLeft => cases focus with
    | leaf => rfl
    | fork p u r => cases r <;> rfl

theorem lift_navigation (f : ρ → τ) (action : Move) (before : Cursor α ρ) (after : Cursor α τ)
    (moved : navigate action (before.mapRecords f) = some after) :
    ∃ target, navigate action before = some target ∧ target.mapRecords f = after := by
  rw [← navigate_mapRecords] at moved
  cases equal : navigate action before with
  | none => simp only [equal,Option.map_none,reduceCtorEq] at moved
  | some target =>
    simp only [equal,Option.map_some,Option.some.injEq] at moved
    exact ⟨target,rfl,moved⟩

theorem plug_inventory_congr (identify : ρ → ι) {before after : Source α ρ}
    (same : before.inventory identify = after.inventory identify) (outside : List (Frame α ρ)) :
    (plug before outside).inventory identify = (plug after outside).inventory identify := by
  induction outside generalizing before after with
  | nil => exact same
  | cons frame rest ih =>
    cases frame with
    | left record sibling => exact ih (by simp only [Source.inventory_fork,same])
    | right sibling record => exact ih (by simp only [Source.inventory_fork,same])

theorem navigate_inventory (identify : ρ → ι) (action : Move) {before after : Cursor α ρ}
    (moved : navigate action before = some after) :
    before.tree.inventory identify = after.tree.inventory identify := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl
  | rotateRight => cases focus with
    | leaf => simp [navigate] at moved
    | fork q l w => cases l with
      | leaf => simp [navigate] at moved
      | fork p u v =>
        cases Option.some.inj moved
        exact plug_inventory_congr identify (by simp only [Source.inventory_fork]; ac_rfl) outside
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [navigate] at moved
      | fork q v w =>
        cases Option.some.inj moved
        exact plug_inventory_congr identify (by simp only [Source.inventory_fork]; ac_rfl) outside

theorem mapRecords_inventory (f : ρ → τ) (identify : τ → ι) (source : Source α ρ) :
    (source.mapRecords f).inventory identify = source.inventory (identify ∘ f) := by
  induction source <;> simp_all [Source.mapRecords,Function.comp_def]

end TangoSquared.Paper20261030
