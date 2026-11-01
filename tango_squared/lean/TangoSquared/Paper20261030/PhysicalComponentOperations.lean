import TangoSquared.Paper20261030.PhysicalWingOperations

/-!
# Combining wing traces and the complete header in one original-key tree

The component root reaches its left wing, right wing, and bottom header
within two edges. Root-to-root wing traces and a reached header rewrite
therefore compose with at most twelve additional operations. Applied to a
source rearrangement, the resulting physical cost is at most `68*b+12`.
The supplied new header is charged as an actual read/write; acquiring its
contents and coordinating the source controller remain separate tasks.
-/

namespace TangoSquared.Paper20261030.PrimaryPhysical

open ColoredStorage SourcePointer

variable {α ρ : Type*}

theorem component_left {before after : Wing α ρ} (right : Wing α ρ) (bottom : α) (header : List ρ)
    {budget : Nat} (execution : ProjectionLocal.Rearranges before after budget) :
    Rearranges (component before right bottom header) (component after right bottom header) (budget+4) := by
  cases before <;> cases after
  · exact rearranges_refl _ _
  · exact False.elim execution
  · exact False.elim execution
  · cases right
    · exact (Rearranges.left execution).mono (by omega)
    · exact (Rearranges.left execution).left

theorem component_right (left : Wing α ρ) {before after : Wing α ρ} (bottom : α) (header : List ρ)
    {budget : Nat} (execution : ProjectionLocal.Rearranges before after budget) :
    Rearranges (component left before bottom header) (component left after bottom header) (budget+2) := by
  cases before <;> cases after
  · exact rearranges_refl _ _
  · exact False.elim execution
  · exact False.elim execution
  · cases left <;> exact Rearranges.right execution

theorem component_header (left right : Wing α ρ) (bottom : α) (before after : List ρ) :
    Rearranges (component left right bottom before) (component left right bottom after) 6 := by
  have update := replace_root (Source.leaf bottom (before.map some)) (after.map some)
  cases left <;> cases right
  · exact update.mono (by decide)
  · exact update.left.mono (by decide)
  · exact update.right.mono (by decide)
  · exact update.right.left

theorem component_rearranges {oldLeft newLeft oldRight newRight : Wing α ρ}
    (bottom : α) (oldHeader newHeader : List ρ) {leftCost rightCost : Nat}
    (left : ProjectionLocal.Rearranges oldLeft newLeft leftCost)
    (right : ProjectionLocal.Rearranges oldRight newRight rightCost) :
    Rearranges (component oldLeft oldRight bottom oldHeader) (component newLeft newRight bottom newHeader)
      (leftCost+rightCost+12) := by
  have first := component_left oldRight bottom oldHeader left
  have second := component_right newLeft bottom oldHeader right
  have last := component_header newLeft newRight bottom oldHeader newHeader
  exact ((first.trans second).trans last).mono (by omega)

end TangoSquared.Paper20261030.PrimaryPhysical

namespace TangoSquared.Paper20261030.PackedPrimary

open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

def Input.physical {t : PrefRouter α} (input : Input t ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) : Source α (List (Option (Datum ρ))) :=
  component (graftWing payload input.completePlan.left) (graftWing payload input.completePlan.right)
    t.terminal input.completeHeader

def Input.withSource {t : PrefRouter α} (input : Input t ρ) (source : Source Nat ρ)
    (sameLeaves : input.source.shape.leaves = source.shape.leaves) : Input t ρ where
  start := input.start
  source := source
  leaves := by rw [← sameLeaves]; exact input.leaves

theorem source_physical_rearranges {t : PrefRouter α} (before after : Input t ρ)
    (sameStart : before.start = after.start)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) {budget : Nat}
    (execution : SourcePointer.Rearranges before.source after.source budget) :
    SourcePointer.Rearranges (before.physical payload) (after.physical payload) (68*budget+12) := by
  have left := left_payload_rearranges before.start t payload execution
  have right := right_payload_rearranges before.start t payload execution
  have startPlan : plan before.start t after.source = plan after.start t after.source := by rw [sameStart]
  rw [startPlan] at left right
  have combined := component_rearranges t.terminal before.completeHeader after.completeHeader left right
  exact combined.mono (by omega)

theorem source_physical_exposure {t : PrefRouter α} (input : Input t ρ) (source : Source Nat ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) {budget : Nat}
    (execution : SourcePointer.Rearranges input.source source budget) :
    SourcePointer.Rearranges (input.physical payload)
      ((input.withSource source execution.leaves).physical payload) (68*budget+12) :=
  source_physical_rearranges input (input.withSource source execution.leaves) rfl payload execution

end TangoSquared.Paper20261030.PackedPrimary
