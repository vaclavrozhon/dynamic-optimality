import TangoSquared.Paper20261030.CanonicalPhysicalHeaders
import TangoSquared.Paper20261030.ObservedSecondaryAccess
import TangoSquared.Paper20261030.RepresentedPrimaryInputs

/-!
# Secondary accesses on the complete original-key component

The charged source access prepares the requested depth and preserves the
actual updated preference representation. Packing its complete trace and
installing the correct complete virtual header gives the physical bound.
The final original-key endpoint can then be visited within five steps.
-/

namespace TangoSquared.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

theorem VisitsLeaf.rearranges {key : α} {before after : Source α ρ} {budget : Nat}
    (visit : VisitsLeaf key before after budget) : Rearranges before after budget := by
  intro ancestors
  obtain ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,first,_,last,bound⟩ := visit ancestors
  exact ⟨_,_,first.append last,bound⟩

end TangoSquared.Paper20261030.SourcePointer

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open PreferredProjection ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition
open PackedPrimary PrimaryWings

variable {α : Type*} [DecidableEq α]

theorem physical_secondary_access {b : Nat} (primary : PrefRouter α) (reference : DepthTree 0 b)
    (pathLength : (exits primary).length = b) (p : DepthSplit → Bool) (request : Nat) (valid : request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference p) component)
    (payload : Exit α → Source α (List (Option (Datum Cached)))) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload))
      (outRep : Represents followsRight (source reference (Secondary.intervalUpdate request p)) out),
      (Secondary.decodeDepth reference (Secondary.intervalUpdate request p)).terminal = request ∧
      SourcePointer.Rearranges
        ((activeInput primary reference p component represented pathLength).physical payload)
        ((activeInput primary reference (Secondary.intervalUpdate request p) out outRep pathLength).physical payload)
        (((Secondary.decodeDepth reference p).accessFlips request+1) *
          (1340000*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+20500)) := by
  obtain ⟨out,outRep,stopped,visit⟩ := access_observed_visits_leaf reference p request
    ⟨Nat.zero_le _,valid⟩ component represented
  refine ⟨out,outRep,Secondary.sentinel_state_terminal reference p request ⟨Nat.zero_le _,valid⟩,?_⟩
  have execution := source_physical_rearranges
    (activeInput primary reference p component represented pathLength)
    (activeInput primary reference (Secondary.intervalUpdate request p) out outRep pathLength)
    rfl payload visit.rearranges
  apply execution.mono
  unfold observedRepairBound
  have factor : 1 ≤ (Secondary.decodeDepth reference p).accessFlips request+1 := by omega
  nlinarith

theorem physical_endpoint_visit {primary : PrefRouter α} (input : Input primary Cached)
    (payload : Exit α → Source α (List (Option (Datum Cached)))) :
    SourcePointer.VisitsLeaf primary.terminal (input.physical payload) (input.physical payload) 5 :=
  PrimaryPhysical.component_header_visit _ _ _ _

end TangoSquared.Paper20261030.SecondaryDecomposition
