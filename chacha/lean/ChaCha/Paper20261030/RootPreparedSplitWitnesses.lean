import ChaCha.Paper20261030.PreparedSplitWitnesses

set_option autoImplicit false

/-! Restoration from a single sentinel split, including the minimum-depth
head switch. At the minimum there is no retained old prefix, and the
incoming sentinel restoration already represents the new active source. -/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses

open ColoredStorage SourcePointer Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition SourceLocalProgram

theorem sentinel_restore {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = d)
    (component right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (high : Cached) (split : Sentinel component d right high) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (suffixSource reference preferences d valid) out ∧
      ∃ reads cost, Run (HeadRestoreController.program false) (HeadRestoreController.initial false)
        ⟨.fork high (terminalLeaf d) right.tree,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310 := by
  rcases split with ⟨found,rfl,rfl⟩
  obtain ⟨out,_,outRep,reads,cost,actual,bound⟩ := PreparedRestoreController.sentinel reference preferences d valid prepared
    component represented found outside
  exact ⟨out,outRep,reads,cost,actual,bound⟩

theorem root_active_restore {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = a)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (incoming right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming)
    (high : Cached) (split : Sentinel incoming a right high) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (source reference (Secondary.spliceBits a oldPreferences incomingPreferences)) out ∧
      ∃ reads cost, Run (HeadRestoreController.program false) (HeadRestoreController.initial false)
        ⟨.fork high (terminalLeaf a) right.tree,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310 := by
  rcases split with ⟨found,rfl,rfl⟩
  exact PreparedRestoreController.root_active reference oldPreferences incomingPreferences preparedOld preparedIncoming incoming incomingRep found outside

theorem root_dormant_restore {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (prepared : (Secondary.decodeDepth reference preferences).terminal = a)
    (old right : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference preferences) old)
    (high : Cached) (split : Sentinel old a right high) (outside) :
    ∃ out : AuxiliaryComponent Nat Nat (Tagged Payload),
      Represents followsRight (suffixSource reference preferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) out ∧
      ∃ reads cost, Run (HeadRestoreController.program false) (HeadRestoreController.initial false)
        ⟨.fork high (terminalLeaf a) right.tree,outside⟩ .done ⟨closed out,outside⟩ reads cost ∧
        cost ≤ 2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310 := by
  apply sentinel_restore reference preferences a ⟨le_rfl,Secondary.reference_bounds reference⟩ prepared old right
  · simpa only [suffixSource_minimum] using oldRep
  · exact split

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedSplitWitnesses
