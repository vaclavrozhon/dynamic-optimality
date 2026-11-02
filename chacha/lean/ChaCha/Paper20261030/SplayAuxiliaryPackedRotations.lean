import ChaCha.Paper20261030.SplayAuxiliaryPhysicalRotations
import ChaCha.Paper20261030.PhysicalPortAgreement

/-!
# A secondary rotation costs at most two physical primary rotations

Each packed wing performs at most one ordinary rotation. Connector and
header records are bookkeeping; the physical tree contains the original
leaf keys. The estimate is independent of the depth of the changed
secondary auxiliary, so no pointer-navigation factor is introduced.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality.SearchRotation
open ColoredStorage RouterProjection ProjectionLocal

variable {α β γ ρ τ C : Type*}

local instance packedRotationColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def projectedShape : Projected α ρ → Router α
  | none => .empty
  | some source => source.shape

@[simp] theorem projectedShape_join (left right : Projected α ρ) :
    projectedShape (ProjectionLocal.join left right) = (projectedShape left).join (projectedShape right) := by
  cases left with
  | none => rfl
  | some left =>
      cases right with
      | none => exact (Router.join_empty _).symm
      | some right => cases left <;> cases right <;> rfl

@[simp] theorem projectedShape_decorate (records : List ρ) (source : Projected α ρ) :
    projectedShape (decorate records source) = projectedShape source := by
  cases source with
  | none => rfl
  | some source => exact SourcePointer.source_setRoot_shape _ _

 theorem physical_projection_rotation [LinearOrder C] (color : α → C) (selected : C)
    (labels : α → β) (values : ρ → τ) (payload : β → Source γ (List (Option τ)))
    (reverse : Bool) {before after : Source α ρ} (rotation : SourceRotation before after) :
    Paper20261030.Router.Step
      (projectedShape (physicalProjection color selected labels values payload reverse before))
      (projectedShape (physicalProjection color selected labels values payload reverse after)) := by
  induction rotation with
  | right a b c x y =>
      cases reverse <;>
        simp only [physicalProjection_fork,Bool.false_eq_true,if_false,if_true,
          projectedShape_decorate,projectedShape_join]
      · exact Paper20261030.Router.step_join_assoc _ _ _
      · exact Paper20261030.Router.step_join_assoc_rev _ _ _
  | left a b c x y =>
      cases reverse <;>
        simp only [physicalProjection_fork,Bool.false_eq_true,if_false,if_true,
          projectedShape_decorate,projectedShape_join]
      · exact Paper20261030.Router.step_join_assoc_rev _ _ _
      · exact Paper20261030.Router.step_join_assoc _ _ _
  | inLeft rotation key right ih =>
      cases reverse <;>
        simp only [physicalProjection_fork,Bool.false_eq_true,if_false,if_true,
          projectedShape_decorate,projectedShape_join] at ih ⊢
      · exact Paper20261030.Router.step_join_left ih _
      · exact Paper20261030.Router.step_join_right _ ih
  | inRight left key rotation ih =>
      cases reverse <;>
        simp only [physicalProjection_fork,Bool.false_eq_true,if_false,if_true,
          projectedShape_decorate,projectedShape_join] at ih ⊢
      · exact Paper20261030.Router.step_join_right _ ih
      · exact Paper20261030.Router.step_join_left ih _

 theorem physical_component_shape (left right : PrimaryPhysical.Wing α ρ)
    (bottom : α) (header : List ρ) :
    (PrimaryPhysical.component left right bottom header).shape =
      ((projectedShape left).join (.leaf bottom)).join (projectedShape right) := by
  have word := congrArg projectedShape (PrimaryPhysical.component_as_join left right bottom header)
  rw [projectedShape_join,projectedShape_join] at word
  exact word

 theorem encoding_tree_shape (encoding : HeadBlocks.Encoding α β γ τ)
    (values : ρ → τ) (source : Source α ρ) :
    (encoding.tree values source).shape =
      ((projectedShape (encoding.wing values true source)).join (.leaf encoding.bottom)).join
        (projectedShape (encoding.wing values false source)) := by
  exact physical_component_shape _ _ _ _

/-- One arbitrary-position source rotation changes the complete packed
component by at most two rotations in the shared original-key BST. -/
theorem packed_source_rotation (encoding : HeadBlocks.Encoding α β γ τ)
    (values : ρ → τ) {before after : Source α ρ} (rotation : SourceRotation before after) :
    ∃ count, Rotations (GapBST.encode (encoding.tree values before))
      (GapBST.encode (encoding.tree values after)) count ∧ count ≤ 2 := by
  let middle := PrimaryPhysical.component (encoding.wing values true after)
    (encoding.wing values false before) encoding.bottom encoding.header
  have firstWing := physical_projection_rotation encoding.color (some true)
    encoding.labels values encoding.payload false rotation
  have secondWing := physical_projection_rotation encoding.color (some false)
    encoding.labels values encoding.payload true rotation
  have first : Paper20261030.Router.Step (encoding.tree values before).shape middle.shape := by
    rw [encoding_tree_shape,show middle.shape = _ from physical_component_shape _ _ _ _]
    exact Paper20261030.Router.step_join_left
      (Paper20261030.Router.step_join_left firstWing _) _
  have second : Paper20261030.Router.Step middle.shape (encoding.tree values after).shape := by
    rw [show middle.shape = _ from physical_component_shape _ _ _ _,encoding_tree_shape]
    exact Paper20261030.Router.step_join_right _ secondWing
  obtain ⟨firstCount,firstExecution,firstBound⟩ := router_step_encoded first
  obtain ⟨secondCount,secondExecution,secondBound⟩ := router_step_encoded second
  exact ⟨firstCount+secondCount,firstExecution.append secondExecution,by omega⟩

 theorem packed_source_rotations (encoding : HeadBlocks.Encoding α β γ τ)
    (values : ρ → τ) {before after : Source α ρ} {work : Nat}
    (rotations : SourceRotations before after work) :
    ∃ count, Rotations (GapBST.encode (encoding.tree values before))
      (GapBST.encode (encoding.tree values after)) count ∧ count ≤ 2*work := by
  induction rotations with
  | refl source => exact ⟨0,.refl _,by omega⟩
  | step rotation rest ih =>
      obtain ⟨first,firstExecution,firstBound⟩ := packed_source_rotation encoding values rotation
      obtain ⟨remaining,remainingExecution,remainingBound⟩ := ih
      exact ⟨first+remaining,firstExecution.append remainingExecution,by omega⟩

end ChaCha.Paper20261030.SplayAuxiliary
