import ChaCha.Paper20261030.SplayAuxiliaryGlobalComponents
import ChaCha.Paper20261030.SplayAuxiliarySecondarySource

/-! Ordinary bottom-up secondary access on one actual persistent component.
The returned forest is the same inventory maintained by the splay proof. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage SecondaryDecomposition PreferredProjection
open MultiSplay.Global.Preferred (Core)

 theorem component_access {a b : Nat} (reference : DepthTree a b) (p : DepthSplit → Bool)
    (request : Nat) (before : Global.Component) (valid : before.Valid (source reference p)) :
    ∃ after : Global.Component, ∃ work : Nat,
      after.Valid (source reference (Secondary.intervalUpdate request p)) ∧
      SourceRotations before.auxiliary.closed after.auxiliary.closed work ∧
      SecondaryExecution reference request (Secondary.decodeDepth reference p)
        (Secondary.decodeDepth reference (Secondary.intervalUpdate request p))
        (referenceCuts id before.auxiliary.closed) (referenceCuts id after.auxiliary.closed) work ∧
      work+2*after.potential ≤ 2*before.potential+
        (24*Nat.log 2 (LocalReferences.depthReference reference).height+3)*
          (Secondary.decodeDepth reference p).accessFlips request := by
  have inventory : Core (routerState (Secondary.decodeDepth reference p))
      (separatorReference reference).toRaw (referenceCuts id before.auxiliary.closed) before.trees := by
    have h := valid.2
    change Core (referenceState followsRight (source reference p))
      (referenceCuts secondaryKey (source reference p)) _ _ at h
    simpa only [referenceState_secondary,referenceCuts_secondary] using h
  obtain ⟨auxiliary,trees,work,represented,inventory,rotations,ordinary,bound⟩ :=
    secondary_source_access reference p request before.auxiliary valid.1 inventory
  refine ⟨⟨auxiliary,trees⟩,work,⟨represented,?_⟩,rotations,ordinary,?_⟩
  · change Core (referenceState followsRight (source reference (Secondary.intervalUpdate request p)))
      (referenceCuts secondaryKey (source reference (Secondary.intervalUpdate request p))) _ _
    simpa only [referenceState_secondary,referenceCuts_secondary] using inventory
  · simpa only [Global.Component.potential,separatorReference_height] using bound

end ChaCha.Paper20261030.SplayAuxiliary
