import ChaCha.Paper20261030.SplayAuxiliaryPhysicalViews
import ChaCha.Paper20261030.SplayAuxiliaryPackedRotations
import ChaCha.Paper20261030.SearchRotationMetadata

/-! Lift arbitrary-position secondary splay rotations into the complete
maintained original-key tree. The surrounding primary payloads stay fixed. -/

namespace ChaCha.Paper20261030.SplayAuxiliary.Physical

open DynamicOptimality.SearchRotation
open ColoredStorage SecondaryDecomposition Decomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical

variable {α : Type*} [DecidableEq α]

 theorem encoding_header_shape {ρ τ : Type*} (start : Nat) (primary : PrefRouter α)
    (payload : Exit α → Source α (List (Option τ))) (old fresh : List τ)
    (values : ρ → τ) (source : Source Nat ρ) :
    ((PackedPrimary.encoding start primary payload old).tree values source).shape =
      ((PackedPrimary.encoding start primary payload fresh).tree values source).shape := by
  rw [encoding_tree_shape,encoding_tree_shape]
  rfl

 theorem maintained_secondary_rotations {height : Nat} (reference : DepthTree 0 height)
    (p q : DepthSplit → Bool) (primary : PrefRouter α) (perfect : primary.Perfect height)
    (distinct : primary.leaves.Nodup) (components : Global.Table α) (fresh : Global.Component)
    (beforeRep : Represents cutKey followsRight (source reference p) (components primary.terminal).auxiliary)
    (afterRep : Represents cutKey followsRight (source reference q) fresh.auxiliary)
    {work : Nat} (ordinary : SourceRotations (closed (components primary.terminal)) (closed fresh) work) :
    ∃ rotations, Rotations (GapBST.encode (physicalState primary components))
      (GapBST.encode (physicalState primary (Function.update components primary.terminal fresh))) rotations ∧
      rotations ≤ 2*work := by
  let payload := storedPayload primary.componentStart components
  let oldInput := active_input primary reference p (components primary.terminal) beforeRep (perfect_exits_length perfect)
  let newInput := active_input primary reference q fresh afterRep (perfect_exits_length perfect)
  let updated := Function.update components primary.terminal fresh
  have oldView : physicalState primary components = oldInput.physical payload :=
    physicalState_as_input primary components oldInput.leaves
  have newView : physicalState primary updated = newInput.physical payload := by
    have valid : ValidInput 0 primary (closed (updated primary.terminal)) := by
      have h : ValidInput 0 primary (closed fresh) := newInput.leaves
      simpa only [updated,Function.update_self] using h
    have view := physicalState_as_input primary updated valid
    have view' : physicalState primary updated = newInput.physical (storedPayload primary.componentStart updated) := by
      simpa only [updated,Function.update_self,newInput,active_input] using view
    exact view'.trans (newInput.physical_payload_congr _ _
      (fun exit member => storedPayload_update_active primary distinct components fresh member))
  obtain ⟨rotations,physical,bound⟩ := packed_source_rotations (oldInput.encoding payload) Datum.record ordinary
  have targetShape : ((oldInput.encoding payload).tree Datum.record (closed fresh)).shape =
      ((newInput.encoding payload).tree Datum.record (closed fresh)).shape :=
    encoding_header_shape 0 primary payload _ _ Datum.record (closed fresh)
  have target := source_shape_encode targetShape
  refine ⟨rotations,?_,bound⟩
  change Rotations (GapBST.encode (physicalState primary components))
    (GapBST.encode (physicalState primary updated)) rotations
  rw [oldView,newView,← oldInput.encoding_tree payload,← newInput.encoding_tree payload]
  change Rotations (GapBST.encode ((oldInput.encoding payload).tree Datum.record (closed (components primary.terminal))))
    (GapBST.encode ((newInput.encoding payload).tree Datum.record (closed fresh))) rotations
  rw [← target]
  exact physical

 theorem source_rearranges_rotations {ρ : Type*} {before after : Source α ρ} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    ∃ rotations, Rotations (GapBST.encode before) (GapBST.encode after) rotations ∧ rotations ≤ budget := by
  obtain ⟨reads,cost,trace,bound⟩ := execution []
  obtain ⟨physicalCost,physical,physicalBound⟩ := GapBST.trace trace
  obtain ⟨rotations,actual,rotationBound⟩ := SearchRotationBridge.pointer_trace_rotations physical
  have beforeTree := GapBST.cursor_tree (SourcePointer.Cursor.mk before [])
  have afterTree := GapBST.cursor_tree (SourcePointer.Cursor.mk after [])
  rw [beforeTree,afterTree] at actual
  exact ⟨rotations,actual,rotationBound.trans (physicalBound.trans bound)⟩

end ChaCha.Paper20261030.SplayAuxiliary.Physical
