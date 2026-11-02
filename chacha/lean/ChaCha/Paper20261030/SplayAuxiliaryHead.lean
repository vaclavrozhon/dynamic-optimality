import ChaCha.Paper20261030.SplayAuxiliaryAccess
import ChaCha.Paper20261030.SplayAuxiliaryExchange
import ChaCha.Paper20261030.SplayAuxiliaryPhysicalExchange
import ChaCha.Paper20261030.SplayAuxiliaryPhysicalSecondary
import ChaCha.Paper20261030.SplayAuxiliaryGlobalPotential
import ChaCha.Paper20261030.MaintainedPhysicalHeadStep

/-!
# One complete ordinary-splay primary head step

First access the requested depth in the active secondary forest, then
exchange the prepared suffixes. The certificate keeps both ordinary-splay
transcripts; the physical endpoint is the full original-key BST. A single
global potential pays for all auxiliary changes, including dormant trees.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality.SearchRotation
open ColoredStorage SecondaryDecomposition PreferredProjection PrimaryWings Secondary

variable {α : Type*} [DecidableEq α]

def headFactor {height : Nat} (reference : DepthTree 0 height) : Nat :=
  10000*(Nat.log 2 (LocalReferences.depthReference reference).height+1)

inductive HeadExecution {height : Nat} (reference : DepthTree 0 height)
    (memory : MemoryKey → Bool) (before after : PrefRouter α) (depth : Nat)
    (components : Global.Table α) : Global.Table α → Prop
  | run {prepared active dormant : Global.Component} {secondaryWork exchangeWork : Nat}
      (secondary : SecondaryExecution reference depth
        (decodeDepth reference (ownerBits before before.terminal memory))
        (decodeDepth reference (intervalUpdate depth (ownerBits before before.terminal memory)))
        (referenceCuts id (components before.terminal).auxiliary.closed)
        (referenceCuts id prepared.auxiliary.closed) secondaryWork)
      (exchange : PreparedExecution prepared.auxiliary (components after.terminal).auxiliary depth
        active.auxiliary dormant.auxiliary exchangeWork) :
      HeadExecution reference memory before after depth components
        (Function.update (Function.update components before.terminal dormant) after.terminal active)

 theorem head_exists {height depth : Nat} (reference : DepthTree 0 height)
    {request : α} {before after : PrefRouter α} (step : PrefRouter.HeadStep request depth before after)
    (perfect : before.Perfect height) (distinct : before.leaves.Nodup)
    (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference before perfect memory components) :
    ∃ out : Global.Table α, ∃ rotations : Nat,
      Global.Table.Valid reference after (step.perfect perfect) (advanceDepth before request depth memory) out ∧
      Rotations (GapBST.encode (Physical.physicalState before components))
        (GapBST.encode (Physical.physicalState after out)) rotations ∧
      HeadExecution reference memory before after depth components out ∧
      rotations+408*Global.Table.potential after.leaves.toFinset out ≤
        408*components.potential before.leaves.toFinset+
          ((decodeDepth reference (ownerBits before before.terminal memory)).accessFlips depth+1)*headFactor reference := by
  have upper := head_depth_lt step perfect
  have depthBound := Nat.le_of_lt upper
  have endpoints := step.endpoints_ne distinct
  obtain ⟨prepared,secondaryWork,preparedValid,sourceRotations,secondaryOrdinary,secondaryBound⟩ :=
    component_access reference (ownerBits before before.terminal memory) depth (components before.terminal) valid.active
  let preparedComponents := Function.update components before.terminal prepared
  let p := intervalUpdate depth (ownerBits before before.terminal memory)
  let q := intervalUpdate depth (ownerBits before after.terminal memory)
  have preparedP := sentinel_state_terminal reference (ownerBits before before.terminal memory) depth
    ⟨Nat.zero_le _,depthBound⟩
  have preparedQ := sentinel_state_terminal reference (ownerBits before after.terminal memory) depth
    ⟨Nat.zero_le _,depthBound⟩
  have incomingValid := valid.incoming reference depthBound step distinct perfect memory components
  obtain ⟨active,dormant,exchangeWork,activeValid,dormantValid,exchangeOrdinary,exchangeBound⟩ :=
    component_exchange reference p q depth upper preparedP preparedQ prepared (components after.terminal)
      preparedValid incomingValid
  let out := Function.update (Function.update components before.terminal dormant) after.terminal active
  have outValid := valid.prepared_head_outputs reference depthBound step distinct perfect memory components
    dormant active activeValid dormantValid
  obtain ⟨firstCount,firstPhysical,firstBound⟩ := Physical.maintained_secondary_rotations reference
    (ownerBits before before.terminal memory) p before perfect distinct components prepared
      valid.active.1 preparedValid.1 sourceRotations
  have activePrepared : Decomposition.Represents cutKey followsRight (source reference p)
      (preparedComponents before.terminal).auxiliary := by
    simpa only [preparedComponents,Function.update_self] using preparedValid.1
  have incomingPrepared : Decomposition.Represents cutKey followsRight
      (suffixSource reference q depth ⟨Nat.zero_le _,depthBound⟩)
      (preparedComponents after.terminal).auxiliary := by
    simpa only [preparedComponents,Function.update_of_ne endpoints.symm] using incomingValid.1
  have actualExchange : PreparedExecution (preparedComponents before.terminal).auxiliary
      (preparedComponents after.terminal).auxiliary depth active.auxiliary dormant.auxiliary exchangeWork := by
    simpa only [preparedComponents,Function.update_self,Function.update_of_ne endpoints.symm] using exchangeOrdinary
  have exchangeTrace := Physical.maintained_prepared_exchange reference p q upper step distinct perfect
    preparedComponents active dormant exchangeWork activePrepared incomingPrepared activeValid.1 dormantValid.1 actualExchange
  have exchangePhysical : SourcePointer.Rearranges (Physical.physicalState before preparedComponents)
      (Physical.physicalState after out) (204*exchangeWork+716) := by
    simpa only [preparedComponents,Function.update_idem] using exchangeTrace
  obtain ⟨lastCount,lastPhysical,lastBound⟩ := Physical.source_rearranges_rotations exchangePhysical
  have firstPotential := Global.Table.single_amortized before.leaves.toFinset components before.terminal
    (List.mem_toFinset.mpr before.terminal_mem) prepared secondaryBound
  have exchangeLocal : exchangeWork+2*(active.potential+dormant.potential) ≤
      2*((preparedComponents before.terminal).potential+(preparedComponents after.terminal).potential)+
        20*Nat.log 2 (LocalReferences.depthReference reference).height+3 := by
    simpa only [preparedComponents,Function.update_self,Function.update_of_ne endpoints.symm] using exchangeBound
  have lastPotential := Global.Table.head_amortized step distinct preparedComponents dormant active (by simpa only [Nat.add_assoc] using exchangeLocal)
  have lastPotential' : exchangeWork+2*Global.Table.potential after.leaves.toFinset out ≤
      2*Global.Table.potential before.leaves.toFinset preparedComponents+
        20*Nat.log 2 (LocalReferences.depthReference reference).height+3 := by
    simpa only [preparedComponents,Function.update_idem,Nat.add_assoc] using lastPotential
  refine ⟨out,firstCount+lastCount,outValid,firstPhysical.append lastPhysical,
    .run secondaryOrdinary exchangeOrdinary,?_⟩
  change secondaryWork+2*Global.Table.potential before.leaves.toFinset preparedComponents ≤ _ at firstPotential
  unfold headFactor
  nlinarith

end ChaCha.Paper20261030.SplayAuxiliary
