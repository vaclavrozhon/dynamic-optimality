import ChaCha.Paper20261030.SplayAuxiliaryPreparedExecution
import ChaCha.Paper20261030.SplayAuxiliaryGlobalSplice
import ChaCha.Paper20261030.SplayAuxiliaryGlobalComponents

/-! Prepared ordinary-splay exchange with the complete persistent forest.
Every descendant inventory is transferred from the actual two inputs. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open ColoredStorage SecondaryDecomposition PreferredProjection

 theorem component_exchange {b : Nat} (reference : DepthTree 0 b) (p q : DepthSplit → Bool)
    (d : Nat) (upper : d < b)
    (preparedP : (Secondary.decodeDepth reference p).terminal = d)
    (preparedQ : (Secondary.decodeDepth reference q).terminal = d)
    (active incoming : Global.Component)
    (activeValid : active.Valid (source reference p))
    (incomingValid : incoming.Valid (suffixSource reference q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩)) :
    ∃ out parked : Global.Component, ∃ work : Nat,
      out.Valid (source reference (Secondary.spliceBits d p q)) ∧
      parked.Valid (suffixSource reference p d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩) ∧
      PreparedExecution active.auxiliary incoming.auxiliary d out.auxiliary parked.auxiliary work ∧
      work+2*(out.potential+parked.potential) ≤ 2*(active.potential+incoming.potential)+
        20*Nat.log 2 (LocalReferences.depthReference reference).height+3 := by
  obtain ⟨out,parked,work,ordinary,outRep,parkedRep,bound⟩ :=
    prepared_execution_exists reference p q d upper preparedP preparedQ active.auxiliary incoming.auxiliary
      activeValid.1 incomingValid.1
  obtain ⟨outPorts,parkedPorts⟩ := ordinary.port_words reference p preparedP activeValid.1
  obtain ⟨outTrees,parkedTrees,outInventory,parkedInventory,potentialEquality⟩ :=
    exchange_inventories reference p q d ⟨Nat.zero_le _,Nat.le_of_lt upper⟩ preparedP preparedQ
      active.auxiliary incoming.auxiliary out parked activeValid.1 incomingValid.1 outRep parkedRep
      outPorts parkedPorts activeValid.2 incomingValid.2
  refine ⟨⟨out,outTrees⟩,⟨parked,parkedTrees⟩,work,⟨outRep,outInventory⟩,
    ⟨parkedRep,parkedInventory⟩,ordinary,?_⟩
  simp only [Global.Component.potential]
  omega

end ChaCha.Paper20261030.SplayAuxiliary
