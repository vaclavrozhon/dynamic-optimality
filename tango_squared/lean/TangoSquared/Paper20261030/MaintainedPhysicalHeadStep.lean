import TangoSquared.Paper20261030.MaintainedPhysicalAccess
import TangoSquared.Paper20261030.MaintainedPhysicalExchange

/-! The complete physical implementation of one primary head step:
prepare its depth in the active secondary component, exchange the tails,
and retain the persistent-memory invariant for every component. -/

namespace TangoSquared.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem head_depth_lt {x : α} {depth height : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x depth before after) (perfect : before.Perfect height) : depth < height := by
  obtain ⟨common,old,incoming,direction,length,_,_,beforeWord,_⟩ := head_exit_decomposition step
  have size := perfect_exits_length perfect
  rw [beforeWord,List.length_append,List.length_cons,length] at size
  omega

end TangoSquared.Paper20261030.PrimaryWings

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection PrimaryWings Secondary

variable {α : Type*} [DecidableEq α]

def physicalHeadBound {height : Nat} (reference : DepthTree 0 height) : Nat :=
  3356000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+28500

theorem maintained_physical_head {height depth : Nat} (reference : DepthTree 0 height)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x depth before after)
    (perfect : before.Perfect height) (distinct : before.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Components α)
    (valid : Components.Valid reference before perfect memory components) :
    ∃ out : Components α,
      Components.Valid reference after (step.perfect perfect) (advanceDepth before x depth memory) out ∧
      SourcePointer.Rearranges (physicalState before components) (physicalState after out)
        (((decodeDepth reference (ownerBits before before.terminal memory)).accessFlips depth+1) *
          physicalHeadBound reference) := by
  have upper := head_depth_lt step perfect
  have depthBound := Nat.le_of_lt upper
  have endpoints := step.endpoints_ne distinct
  obtain ⟨preparedActive,activeRep,accessTrace⟩ := maintained_physical_access reference before perfect distinct
    memory components valid depth depthBound
  let preparedComponents := Function.update components before.terminal preparedActive
  let p := intervalUpdate depth (ownerBits before before.terminal memory)
  let q := intervalUpdate depth (ownerBits before after.terminal memory)
  have preparedP := sentinel_state_terminal reference (ownerBits before before.terminal memory) depth
    ⟨Nat.zero_le _,depthBound⟩
  have preparedQ := sentinel_state_terminal reference (ownerBits before after.terminal memory) depth
    ⟨Nat.zero_le _,depthBound⟩
  have incomingMember : after.terminal ∈ before.leaves := by rw [← step.leaves]; exact after.terminal_mem
  have incomingRep : Represents followsRight
      (suffixSource reference q depth ⟨Nat.zero_le _,depthBound⟩) (components after.terminal) := by
    have rep := valid after.terminal incomingMember
    simpa only [componentSource,if_neg endpoints.symm,step.incoming_componentStart distinct,Nat.add_sub_cancel_right] using rep
  have activePrepared : Represents followsRight (source reference p) (preparedComponents before.terminal) := by
    simpa only [preparedComponents,Function.update_self] using activeRep
  have incomingPrepared : Represents followsRight
      (suffixSource reference q depth ⟨Nat.zero_le _,depthBound⟩) (preparedComponents after.terminal) := by
    simpa only [preparedComponents,Function.update_of_ne endpoints.symm] using incomingRep
  let exchanged := exchange reference p depth preparedP preparedActive (components after.terminal) activeRep
  let out := Function.update (Function.update components before.terminal exchanged.2) after.terminal exchanged.1
  have outValid := valid.head_exchange reference depthBound step distinct perfect memory components preparedActive activeRep
  have exchangeTrace := maintained_prepared_exchange reference p q upper preparedP preparedQ step distinct perfect
    preparedComponents activePrepared incomingPrepared
  have physicalExchange : SourcePointer.Rearranges (physicalState before preparedComponents) (physicalState after out)
      (2016000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+8000) := by
    simpa only [preparedComponents,Function.update_self,Function.update_of_ne endpoints.symm,Function.update_idem]
      using exchangeTrace
  refine ⟨out,outValid,?_⟩
  apply (accessTrace.trans physicalExchange).mono
  unfold physicalHeadBound
  have positive : 1 ≤ (decodeDepth reference (ownerBits before before.terminal memory)).accessFlips depth+1 := by omega
  nlinarith

end TangoSquared.Paper20261030.SecondaryDecomposition
