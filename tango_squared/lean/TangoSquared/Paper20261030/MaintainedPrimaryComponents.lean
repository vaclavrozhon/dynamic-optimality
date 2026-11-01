import TangoSquared.Paper20261030.DormantMemoryFrame
import TangoSquared.Paper20261030.CanonicalPreparedExchange
import TangoSquared.Paper20261030.HeadExchangeMemory

/-!
# The shared invariant for all endpoint-indexed secondary components

Each original key is the endpoint of one preferred path. Its component
stores the full reference when active, and the prepared suffix beginning
one depth before its path start when dormant. Genuine preferences are
read from the existing owner-indexed persistent memory.
-/

namespace TangoSquared.Paper20261030.Secondary

theorem intervalUpdate_idempotent (d : Nat) (p : DepthSplit → Bool) :
    intervalUpdate d (intervalUpdate d p) = intervalUpdate d p := by
  funext split
  simp only [intervalUpdate]
  split_ifs <;> rfl

end TangoSquared.Paper20261030.Secondary

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection Secondary

variable {α : Type*} [DecidableEq α]

abbrev Components (α : Type*) := α → AuxiliaryComponent Nat Nat (Tagged Payload)

def componentSource {height : Nat} (reference : DepthTree 0 height) (primary : PrefRouter α)
    (perfect : primary.Perfect height) (memory : MemoryKey → Bool) (key : α) : Source Nat Cached :=
  if key = primary.terminal then source reference (ownerBits primary key memory)
  else
    let sentinel := primary.componentStart key - 1
    suffixSource reference (intervalUpdate sentinel (ownerBits primary key memory)) sentinel
      ⟨Nat.zero_le _,by have bound := PrefRouter.componentStart_le_height perfect key; omega⟩

def Components.Valid {height : Nat} (reference : DepthTree 0 height) (primary : PrefRouter α)
    (perfect : primary.Perfect height) (memory : MemoryKey → Bool) (components : Components α) : Prop :=
  ∀ key ∈ primary.leaves, Represents followsRight (componentSource reference primary perfect memory key) (components key)

theorem componentSource_active {height : Nat} (reference : DepthTree 0 height) (primary : PrefRouter α)
    (perfect : primary.Perfect height) (memory : MemoryKey → Bool) :
    componentSource reference primary perfect memory primary.terminal = source reference (ownerBits primary primary.terminal memory) := by
  simp [componentSource]

theorem componentSource_other {height d : Nat} (reference : DepthTree 0 height)
    {x key : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (perfect : before.Perfect height) (member : key ∈ before.leaves)
    (oldOther : key ≠ before.terminal) (newOther : key ≠ after.terminal) (memory : MemoryKey → Bool) :
    componentSource reference after (step.perfect perfect) (advanceDepth before x d memory) key =
      componentSource reference before perfect memory key := by
  have startSame := step.componentStart_unchanged key oldOther newOther
  simp only [componentSource,if_neg oldOther,if_neg newOther,startSame]
  apply prepared_suffix_congr
  intro split memberSplit afterSentinel
  have startPositive : 0 < before.componentStart key :=
    Nat.pos_of_ne_zero (fun h => oldOther ((PrefRouter.componentStart_zero_iff member).mp h))
  have bounds := reference.node_bounds memberSplit
  exact head_dormant_genuine_unchanged step distinct perfect member oldOther memory split
    (by omega) (by omega)

theorem prepared_exchange_memory_represents {height d : Nat} (reference : DepthTree 0 height) (depth : d ≤ height)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (memory : MemoryKey → Bool)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight
      (source reference (intervalUpdate d (ownerBits before before.terminal memory))) active)
    (incomingRep : Represents followsRight
      (suffixSource reference (intervalUpdate d (ownerBits before after.terminal memory))
        d ⟨Nat.zero_le _,depth⟩) incoming) :
    let p := intervalUpdate d (ownerBits before before.terminal memory)
    let prepared := sentinel_state_terminal reference (ownerBits before before.terminal memory) d ⟨Nat.zero_le _,depth⟩
    let out := exchange reference p d prepared active incoming activeRep
    Represents followsRight (source reference (ownerBits after after.terminal (advanceDepth before x d memory))) out.1 ∧
    Represents followsRight (suffixSource reference (ownerBits after before.terminal (advanceDepth before x d memory))
      d ⟨Nat.zero_le _,depth⟩) out.2 := by
  dsimp only
  let p := intervalUpdate d (ownerBits before before.terminal memory)
  let q := intervalUpdate d (ownerBits before after.terminal memory)
  have hp := sentinel_state_terminal reference (ownerBits before before.terminal memory) d ⟨Nat.zero_le _,depth⟩
  have hq := sentinel_state_terminal reference (ownerBits before after.terminal memory) d ⟨Nat.zero_le _,depth⟩
  obtain ⟨newRep,oldRep⟩ := exchange_represents reference p q d ⟨Nat.zero_le _,depth⟩ hp hq active incoming activeRep incomingRep
  constructor
  · rw [head_memory_transfer step distinct memory]
    rw [splice_prepared_suffix] at newRep
    exact newRep
  · rw [old_tail_prepared step distinct memory]
    exact oldRep

theorem Components.Valid.head_exchange {height d : Nat} (reference : DepthTree 0 height) (depth : d ≤ height)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (perfect : before.Perfect height) (memory : MemoryKey → Bool)
    (components : Components α) (valid : Components.Valid reference before perfect memory components)
    (preparedActive : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight
      (source reference (intervalUpdate d (ownerBits before before.terminal memory))) preparedActive) :
    let p := intervalUpdate d (ownerBits before before.terminal memory)
    let prepared := sentinel_state_terminal reference (ownerBits before before.terminal memory) d ⟨Nat.zero_le _,depth⟩
    let out := exchange reference p d prepared preparedActive (components after.terminal) activeRep
    Components.Valid reference after (step.perfect perfect) (advanceDepth before x d memory)
      (Function.update (Function.update components before.terminal out.2) after.terminal out.1) := by
  dsimp only
  have endpoints := step.endpoints_ne distinct
  have incomingMember : after.terminal ∈ before.leaves := by rw [← step.leaves]; exact after.terminal_mem
  have incomingRep : Represents followsRight
      (suffixSource reference (intervalUpdate d (ownerBits before after.terminal memory))
        d ⟨Nat.zero_le _,depth⟩) (components after.terminal) := by
    have represented := valid after.terminal incomingMember
    simpa only [componentSource,if_neg endpoints.symm,step.incoming_componentStart distinct,Nat.add_sub_cancel_right]
      using represented
  let p := intervalUpdate d (ownerBits before before.terminal memory)
  have prepared := sentinel_state_terminal reference (ownerBits before before.terminal memory) d ⟨Nat.zero_le _,depth⟩
  let out := exchange reference p d prepared preparedActive (components after.terminal) activeRep
  obtain ⟨newRep,oldRep⟩ := prepared_exchange_memory_represents reference depth step distinct memory
    preparedActive (components after.terminal) activeRep incomingRep
  intro key member
  by_cases isNew : key = after.terminal
  · subst key
    simpa only [Function.update_self,componentSource_active] using newRep
  · by_cases isOld : key = before.terminal
    · subst key
      have preparedOld : intervalUpdate d (ownerBits after before.terminal (advanceDepth before x d memory)) =
          ownerBits after before.terminal (advanceDepth before x d memory) := by
        rw [old_tail_prepared step distinct memory]
        exact intervalUpdate_idempotent _ _
      simpa only [Function.update_of_ne endpoints,Function.update_self,componentSource,if_neg endpoints,
        step.old_componentStart distinct,Nat.add_sub_cancel_right,preparedOld] using oldRep
    · have oldMember : key ∈ before.leaves := by rw [← step.leaves]; exact member
      have frame := componentSource_other reference step distinct perfect oldMember isOld isNew memory
      simpa only [Function.update_of_ne isNew,Function.update_of_ne isOld,frame] using valid key oldMember

end TangoSquared.Paper20261030.SecondaryDecomposition
