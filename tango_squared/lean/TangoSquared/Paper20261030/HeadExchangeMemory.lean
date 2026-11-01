import TangoSquared.Paper20261030.PreparedHeadExchange

/-!
# Prepared component exchange preserves the actual owner-indexed memory

Instantiate the balanced exchange with the persistent bits before an
actual primary `HeadStep`. The preceding secondary access has already
performed `advanceDepth`. Both successor components interpret that same
memory array at their new owners; the exchange introduces no secondary
write or initialization. This identifies the computed component outputs
with the existing counting process, without a simulation-cost assumption.
-/

namespace TangoSquared.Paper20261030.Secondary

theorem splice_prepared_suffix (d : Nat) (p q : DepthSplit → Bool) :
    spliceBits d p (intervalUpdate d q) = spliceBits d p q := by
  funext s
  by_cases before : s.lo ≤ d
  · simp only [spliceBits,if_pos before]
  · simp only [spliceBits,if_neg before,intervalUpdate,
      if_neg (show ¬(s.lo ≤ d ∧ d ≤ s.hi) by omega)]

end TangoSquared.Paper20261030.Secondary

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

variable {α : Type*} [DecidableEq α]

theorem head_exchange_memory {b d : Nat} (reference : DepthTree 0 b) (depth : d ≤ b)
    {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (distinct : before.leaves.Nodup)
    (memory : Secondary.MemoryKey → Bool)
    (active incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight
      (source reference (Secondary.intervalUpdate d (Secondary.ownerBits before before.terminal memory))) active)
    (incomingRep : Represents followsRight
      (suffixSource reference (Secondary.intervalUpdate d (Secondary.ownerBits before after.terminal memory))
        d ⟨Nat.zero_le _,depth⟩) incoming) :
    ∃ (newActive oldDormant : AuxiliaryComponent Nat Nat (Tagged Payload)),
      Represents followsRight
        (source reference (Secondary.ownerBits after after.terminal (Secondary.advanceDepth before x d memory))) newActive ∧
      Represents followsRight
        (suffixSource reference (Secondary.ownerBits after before.terminal (Secondary.advanceDepth before x d memory))
          d ⟨Nat.zero_le _,depth⟩) oldDormant ∧
      newActive.core.toListModel = active.core.toListModel ∧
      oldDormant.core.toListModel = incoming.core.toListModel := by
  let p := Secondary.intervalUpdate d (Secondary.ownerBits before before.terminal memory)
  let q := Secondary.intervalUpdate d (Secondary.ownerBits before after.terminal memory)
  let valid : 0 ≤ d ∧ d ≤ b := ⟨Nat.zero_le _,depth⟩
  have hp : (Secondary.decodeDepth reference p).terminal = d :=
    Secondary.sentinel_state_terminal reference _ d valid
  have hq : (Secondary.decodeDepth reference q).terminal = d :=
    Secondary.sentinel_state_terminal reference _ d valid
  let out := exchange reference p d hp active incoming activeRep
  obtain ⟨newRep,oldRep⟩ := exchange_represents reference p q d valid hp hq active incoming activeRep incomingRep
  obtain ⟨newWord,oldWord⟩ := exchange_record_words reference p q d valid hp hq active incoming activeRep incomingRep
  refine ⟨out.1,out.2,?_,?_,newWord,oldWord⟩
  · rw [Secondary.head_memory_transfer step distinct memory]
    have same : Secondary.spliceBits d p q = Secondary.spliceBits d p
        (Secondary.ownerBits before after.terminal memory) := Secondary.splice_prepared_suffix d p _
    rw [same] at newRep
    exact newRep
  · rw [Secondary.old_tail_prepared step distinct memory]
    exact oldRep

end TangoSquared.Paper20261030.SecondaryDecomposition
