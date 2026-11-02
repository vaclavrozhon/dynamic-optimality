import ChaCha.Paper20261030.MaintainedPrimaryComponents
import ChaCha.Paper20261030.GlobalPrimaryInventory

set_option autoImplicit false

/-! The endpoint table is updated from the outputs of an actual local head
program. The proof uses their source representations, not equality with
the noncomputable balanced exchange chosen in the earlier trace theorem.
All other endpoint components are retained literally. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection Secondary

variable {α : Type*} [DecidableEq α]

theorem Components.Valid.head_outputs {height d : Nat} (reference : DepthTree 0 height)
    (depth : d ≤ height) {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (components : Components α) (valid : Components.Valid reference before perfect memory components)
    (dormant active : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight
      (source reference (ownerBits after after.terminal (advanceDepth before x d memory))) active)
    (dormantRep : Represents followsRight
      (suffixSource reference (ownerBits after before.terminal (advanceDepth before x d memory))
        d ⟨Nat.zero_le _,depth⟩) dormant) :
    Components.Valid reference after (step.perfect perfect) (advanceDepth before x d memory)
      (Function.update (Function.update components before.terminal dormant) after.terminal active) := by
  have endpoints := step.endpoints_ne distinct
  intro key member
  by_cases isNew : key = after.terminal
  · subst key
    simpa only [Function.update_self,componentSource_active] using activeRep
  · by_cases isOld : key = before.terminal
    · subst key
      have preparedOld : intervalUpdate d (ownerBits after before.terminal (advanceDepth before x d memory)) =
          ownerBits after before.terminal (advanceDepth before x d memory) := by
        rw [old_tail_prepared step distinct memory]
        exact intervalUpdate_idempotent _ _
      simpa only [Function.update_of_ne endpoints,Function.update_self,componentSource,if_neg endpoints,
        step.old_componentStart distinct,Nat.add_sub_cancel_right,preparedOld] using dormantRep
    · have oldMember : key ∈ before.leaves := by rw [← step.leaves]; exact member
      have frame := componentSource_other reference step distinct perfect oldMember isOld isNew memory
      simpa only [Function.update_of_ne isNew,Function.update_of_ne isOld,frame] using valid key oldMember

/-- The prepared preference splice returned by both concrete head programs
is the owner-memory update used by the primary counting process. -/
theorem Components.Valid.prepared_head_outputs {height d : Nat} (reference : DepthTree 0 height)
    (depth : d ≤ height) {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (components : Components α) (valid : Components.Valid reference before perfect memory components)
    (dormant active : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight
      (source reference (spliceBits d
        (intervalUpdate d (ownerBits before before.terminal memory))
        (intervalUpdate d (ownerBits before after.terminal memory)))) active)
    (dormantRep : Represents followsRight
      (suffixSource reference (intervalUpdate d (ownerBits before before.terminal memory))
        d ⟨Nat.zero_le _,depth⟩) dormant) :
    Components.Valid reference after (step.perfect perfect) (advanceDepth before x d memory)
      (Function.update (Function.update components before.terminal dormant) after.terminal active) := by
  apply valid.head_outputs reference depth step distinct perfect memory components dormant active
  · rw [head_memory_transfer step distinct memory]
    rw [splice_prepared_suffix] at activeRep
    exact activeRep
  · rw [old_tail_prepared step distinct memory]
    exact dormantRep

/-- The finite endpoint index set is unchanged by a primary head step. -/
theorem head_endpoint_finset {d : Nat} {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) : after.leaves.toFinset = before.leaves.toFinset := by
  rw [step.leaves]

/-- Apply the local head program's combined logical-inventory equality to
the entire endpoint table, including components outside the two outputs. -/
theorem head_inventory_unique {η : Type*} {d : Nat} {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (owned : α → Multiset η) (unique : GlobalPrimaryInventory.Unique before.leaves.toFinset owned)
    (dormant active : Multiset η)
    (pair : active + dormant = owned before.terminal + owned after.terminal) :
    GlobalPrimaryInventory.Unique after.leaves.toFinset
      (Function.update (Function.update owned before.terminal dormant) after.terminal active) := by
  rw [head_endpoint_finset step]
  apply unique.update_pair
  · exact List.mem_toFinset.mpr before.terminal_mem
  · apply List.mem_toFinset.mpr
    rw [← step.leaves]
    exact after.terminal_mem
  · exact step.endpoints_ne distinct
  · exact pair

theorem head_joint_inventory {η : Type*} {d : Nat} {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (owned : α → Multiset η) (unique : GlobalPrimaryInventory.Unique before.leaves.toFinset owned) :
    (owned before.terminal + owned after.terminal).Nodup := by
  apply unique.pair
  · exact List.mem_toFinset.mpr before.terminal_mem
  · apply List.mem_toFinset.mpr
    rw [← step.leaves]
    exact after.terminal_mem
  · exact step.endpoints_ne distinct

end ChaCha.Paper20261030.SecondaryDecomposition
