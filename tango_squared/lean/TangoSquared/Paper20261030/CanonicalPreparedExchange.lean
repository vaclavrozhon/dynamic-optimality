import TangoSquared.Paper20261030.PerfectPrimaryPorts
import TangoSquared.Paper20261030.RepresentedPrimaryInputs
import TangoSquared.Paper20261030.CompleteComponentInvariant

/-!
# Prepared exchange with the actual bounded complete virtual headers

Both active and dormant input leaf-word invariants follow from maintained
secondary representations and the heights of the actual primary exits.
The supplied total header function therefore selects the actual complete
header at every endpoint. The physical trace has the exact closed
component outputs, without an arbitrary header choice at its endpoints.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PreferredProjection PrimaryWings PackedPrimary

variable {α : Type*} [DecidableEq α]

theorem canonical_prepared_exchange {b : Nat} (reference : DepthTree 0 b)
    (p q : DepthSplit → Bool) (d : Nat) (upper : d < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incomingComponent : AuxiliaryComponent Nat Nat (Tagged Payload))
    (activeRep : Represents followsRight (source reference p) active)
    (incomingRep : Represents followsRight
      (suffixSource reference q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) incomingComponent)
    {x : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep x d before after)
    (distinct : before.leaves.Nodup) (perfect : before.Perfect b)
    (payload : Exit α → Source α (List (Option (Datum Cached)))) :
    ∃ (old incoming : PrefRouter α) (direction : Bool),
      portAt 0 (exits before) d = some ⟨direction,incoming⟩ ∧
      portAt 0 (exits after) d = some ⟨!direction,old⟩ ∧
      let out := exchange reference p d preparedP active incomingComponent activeRep
      ValidInput 0 before (closed active) ∧
      ValidInput (d+1) incoming (closed incomingComponent) ∧
      ValidInput 0 after (closed out.1) ∧
      ValidInput (d+1) old (closed out.2) ∧
      SourcePointer.Rearranges
        (nestedTree Datum.record payload canonicalHeaders before incoming direction d (closed active) (closed incomingComponent))
        (nestedTree Datum.record payload canonicalHeaders after old (!direction) d (closed out.1) (closed out.2))
        (2016000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+8000) ∧
      Represents followsRight (source reference (Secondary.spliceBits d p q)) out.1 ∧
      Represents followsRight (suffixSource reference p d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) out.2 := by
  obtain ⟨old,incoming,direction,oldPort,newPort,execution,newRep,oldRep⟩ :=
    prepared_physical_head_exchange reference p q d upper preparedP preparedQ active incomingComponent
      activeRep incomingRep step distinct Datum.record payload canonicalHeaders
  have afterPerfect := step.perfect perfect
  have beforeLength := perfect_exits_length perfect
  have afterLength := perfect_exits_length afterPerfect
  have incomingLength := perfect_port_length perfect oldPort
  have oldLength := perfect_port_length afterPerfect newPort
  let out := exchange reference p d preparedP active incomingComponent activeRep
  have validStart : d+1 ≤ b := by omega
  have validIncoming : ValidInput (d+1) incoming (closed incomingComponent) :=
    (dormantInput incoming reference (Nat.zero_lt_succ d) validStart q incomingComponent incomingRep incomingLength).leaves
  have validOld : ValidInput (d+1) old (closed out.2) :=
    (dormantInput old reference (Nat.zero_lt_succ d) validStart p out.2 oldRep oldLength).leaves
  exact ⟨old,incoming,direction,oldPort,newPort,
    (activeInput before reference p active activeRep beforeLength).leaves,validIncoming,
    (activeInput after reference (Secondary.spliceBits d p q) out.1 newRep afterLength).leaves,validOld,
    execution,newRep,oldRep⟩

end TangoSquared.Paper20261030.SecondaryDecomposition
