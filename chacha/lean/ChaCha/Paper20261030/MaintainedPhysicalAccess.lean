import ChaCha.Paper20261030.StoredComponentViews
import ChaCha.Paper20261030.PhysicalSecondaryAccess

/-! A secondary access now acts on the complete maintained physical tree.
Only its active endpoint's component-table entry is replaced; the actual
representations of all hanging primary components stay fixed. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection PrimaryWings PackedPrimary PrimaryPhysical Secondary

variable {α : Type*} [DecidableEq α]

theorem physicalState_update_active (primary : PrefRouter α) (distinct : primary.leaves.Nodup)
    (components : Components α) (fresh : AuxiliaryComponent Nat Nat (Tagged Payload))
    (valid : ValidInput 0 primary (closed fresh)) :
    physicalState primary (Function.update components primary.terminal fresh) =
      (Input.mk 0 (closed fresh) valid).physical (storedPayload primary.componentStart components) := by
  let updated := Function.update components primary.terminal fresh
  have updatedValid : ValidInput 0 primary (closed (updated primary.terminal)) := by
    simpa only [updated,Function.update_self] using valid
  rw [physicalState_as_input primary updated updatedValid]
  have same := (Input.mk 0 (closed (updated primary.terminal)) updatedValid).physical_payload_congr
    (storedPayload primary.componentStart updated) (storedPayload primary.componentStart components)
    (fun _ member => storedPayload_update_active primary distinct components fresh member)
  simpa only [updated,Function.update_self] using same

theorem maintained_physical_access {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (distinct : primary.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Components α)
    (valid : Components.Valid reference primary perfect memory components)
    (request : Nat) (depth : request ≤ height) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload))
      (outRep : Represents followsRight
        (source reference (intervalUpdate request (ownerBits primary primary.terminal memory))) out),
      SourcePointer.Rearranges (physicalState primary components)
        (physicalState primary (Function.update components primary.terminal out))
        (((decodeDepth reference (ownerBits primary primary.terminal memory)).accessFlips request+1) *
          (1340000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+20500)) := by
  have represented := valid primary.terminal primary.terminal_mem
  rw [componentSource_active] at represented
  have pathLength := perfect_exits_length perfect
  obtain ⟨out,outRep,_,execution⟩ := physical_secondary_access primary reference pathLength
    (ownerBits primary primary.terminal memory) request depth (components primary.terminal) represented
    (storedPayload primary.componentStart components)
  refine ⟨out,outRep,?_⟩
  have beforeValid := (activeInput primary reference (ownerBits primary primary.terminal memory)
    (components primary.terminal) represented pathLength).leaves
  have afterValid := (activeInput primary reference (intervalUpdate request (ownerBits primary primary.terminal memory))
    out outRep pathLength).leaves
  rw [physicalState_as_input primary components beforeValid,
    physicalState_update_active primary distinct components out afterValid]
  exact execution

end ChaCha.Paper20261030.SecondaryDecomposition
