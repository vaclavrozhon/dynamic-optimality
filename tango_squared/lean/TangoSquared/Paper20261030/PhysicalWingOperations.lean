import TangoSquared.Paper20261030.CompletePrimaryHeaders
import TangoSquared.Paper20261030.PackedRearrangements

/-!
# Charged source operations on the actual original-key routing wings

Project a root-to-root source operation, relabel its retained depth ports
by their actual exits, and attach the unchanged original-key payloads.
The actual trace costs at most 34 times the source budget per real wing.
Right wings are mirrored before attaching payloads. These are physical
trace correspondences; executing their control with bounded registers is
part of the complete controller composition.
-/

namespace TangoSquared.Paper20261030.ProjectionLocal

open ColoredStorage

variable {α β ρ τ : Type*}

theorem Rearranges.relabel (labels : α → β) {before after : Projected α ρ} {budget : Nat}
    (execution : Rearranges before after budget) :
    Rearranges (before.map (Source.relabel labels)) (after.map (Source.relabel labels)) budget := by
  cases before <;> cases after
  · trivial
  · exact False.elim execution
  · exact False.elim execution
  · exact SourcePointer.Rearranges.relabel labels execution

theorem Rearranges.mapRecords (values : ρ → τ) {before after : Projected α ρ} {budget : Nat}
    (execution : Rearranges before after budget) :
    Rearranges (before.map (Source.mapRecords (List.map values)))
      (after.map (Source.mapRecords (List.map values))) budget := by
  cases before <;> cases after
  · trivial
  · exact False.elim execution
  · exact False.elim execution
  · exact SourcePointer.Rearranges.mapRecords (List.map values) execution

theorem Rearranges.graft (payload : α → Source β (List (Option ρ)))
    {before after : Projected α ρ} {budget : Nat} (execution : Rearranges before after budget) :
    Rearranges (before.map (SourcePayloads.graft payload)) (after.map (SourcePayloads.graft payload)) (2*budget) := by
  cases before <;> cases after
  · trivial
  · exact False.elim execution
  · exact False.elim execution
  · exact SourcePayloads.rearranges payload execution

end TangoSquared.Paper20261030.ProjectionLocal

namespace TangoSquared.Paper20261030.PackedPrimary

open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

local instance physicalWingColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem wing_rearranges (start : Nat) (primary : PrefRouter α) (side : Bool)
    {before after : Source Nat ρ} {budget : Nat} (execution : SourcePointer.Rearranges before after budget) :
    ProjectionLocal.Rearranges (wing start primary side before) (wing start primary side after) (17*budget) :=
  (packed_rearranges (color start primary) (some side) execution).relabel (label start primary)

theorem complete_wing_rearranges (start : Nat) (primary : PrefRouter α) (side : Bool)
    {before after : Source Nat ρ} {budget : Nat} (execution : SourcePointer.Rearranges before after budget) :
    ProjectionLocal.Rearranges (liftWing (wing start primary side before))
      (liftWing (wing start primary side after)) (17*budget) :=
  (wing_rearranges start primary side execution).mapRecords Datum.record

theorem left_payload_rearranges (start : Nat) (primary : PrefRouter α)
    (payload : Exit α → Source α (List (Option (Datum ρ))))
    {before after : Source Nat ρ} {budget : Nat} (execution : SourcePointer.Rearranges before after budget) :
    ProjectionLocal.Rearranges (graftWing payload (liftWing (plan start primary before).left))
      (graftWing payload (liftWing (plan start primary after).left)) (34*budget) := by
  simpa only [graftWing,plan,← Nat.mul_assoc] using (complete_wing_rearranges start primary true execution).graft payload

theorem right_payload_rearranges (start : Nat) (primary : PrefRouter α)
    (payload : Exit α → Source α (List (Option (Datum ρ))))
    {before after : Source Nat ρ} {budget : Nat} (execution : SourcePointer.Rearranges before after budget) :
    ProjectionLocal.Rearranges (graftWing payload (liftWing (plan start primary before).right))
      (graftWing payload (liftWing (plan start primary after).right)) (34*budget) := by
  have mirrored := (wing_rearranges start primary false execution).mirror
  have lifted := mirrored.mapRecords Datum.record
  simpa only [graftWing,liftWing,plan,ProjectionLocal.mirror,← Nat.mul_assoc] using lifted.graft payload

end TangoSquared.Paper20261030.PackedPrimary
