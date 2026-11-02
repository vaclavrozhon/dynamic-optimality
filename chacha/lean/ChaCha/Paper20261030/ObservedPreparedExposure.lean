import ChaCha.Paper20261030.CompiledPreparedExposure
import ChaCha.Paper20261030.ComponentBoundaryContinuation
import ChaCha.Paper20261030.IdentifiedBoundaryViews

set_option autoImplicit false

/-!
# Prepared exposure followed by actual boundary reads

The split controller and boundary observer are one program. The observer
starts from the compiler's final root register; its final scalar state
contains the exact boundary records used by the head-switch calculation.
The tagged boundary decomposition is recovered from the actual exposed
source, so its records and subtrees agree with the returned forest.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors
open PreparedExposureExecution (Logical Datum)

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem active {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (lower : a < d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component) (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config) :
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached),
      ∃ lowId highId terminalId, ∃ taggedHead taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig reads cost,
      low.2.1 = d-1 ∧ high.2.1 = d ∧ Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      taggedHead.mapRecords Prod.snd = left.tree ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (ComponentBoundaryContinuation.program (AdjacentExposureController.program (d-1)) true decorated.rootRecord.1)
        (ComponentBoundaryContinuation.initial (AdjacentExposureController.program (d-1)) true decorated.rootRecord.1 (.first .start)) config
        (.second lowId (ComponentObserverCompiler.ready
          (BoundaryReadController.activeResult Prod.fst color (lowId,low) (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail) lowId)) finalConfig reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (lowId,low) taggedHead
          (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail)),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(80220*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+4)+87360 := by
  obtain ⟨left,right,low,high,target,exposedForest,exposedConfig,frontReads,frontCost,lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,
    exposed,targetErases,ids,exposedRep,exposedUnique,exposedAssembly,_,_,frontBound⟩ :=
    PreparedExposureExecution.active reference preferences d terminal lower upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled
  obtain ⟨lowId,highId,terminalId,taggedHead,taggedTail,targetEq,headEq,tailEq⟩ :=
    IdentifiedBoundaryViews.active target low high (terminalLeaf d).rootRecord d left.tree right.tree targetErases
  have targetUnique : (target.inventory Prod.fst).Nodup := by rw [ids]; exact logicalUnique
  rw [targetEq] at exposed exposedRep targetUnique
  obtain ⟨finalForest,finalConfig,reads,cost,actual,finalRep,finalUnique,finalAssembly,wellFormed,bound⟩ :=
    ComponentBoundaryContinuation.active (AdjacentExposureController.program (d-1)) (.first .start) .done decorated.rootRecord.1
      color (lowId,low) (highId,high) (terminalId,(terminalLeaf d).rootRecord) d taggedHead taggedTail targetUnique
      exposedForest exposedRep exposedUnique headerKey payload config exposedConfig exposed exposedAssembly
  exact ⟨left,right,low,high,lowId,highId,terminalId,taggedHead,taggedTail,finalForest,finalConfig,reads,cost,
    lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,headEq,tailEq,actual,finalRep,finalUnique,finalAssembly,wellFormed,by omega⟩

theorem sentinel {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (terminal : (Secondary.decodeDepth reference preferences).terminal = d) (upper : d < b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component) (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config) :
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached),
      ∃ highId terminalId, ∃ taggedTail : Source Nat (η × Cached), ∃ finalForest finalConfig reads cost,
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧ taggedTail.mapRecords Prod.snd = right.tree ∧
      MultiSourceProgram.Run
        (ComponentBoundaryContinuation.program (OpenSplitController.program d) false decorated.rootRecord.1)
        (ComponentBoundaryContinuation.initial (OpenSplitController.program d) false decorated.rootRecord.1 .start) config
        (.second highId (ComponentObserverCompiler.ready
          (BoundaryReadController.sentinelResult Prod.fst color (highId,high)
            (terminalId,(terminalLeaf d).rootRecord) d taggedTail) highId)) finalConfig reads cost ∧
      ProjectionForest.Represents color
        ⟨annotate Prod.fst color none (.fork (highId,high) (.leaf d (terminalId,(terminalLeaf d).rootRecord)) taggedTail),[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2)+49920 := by
  obtain ⟨right,high,target,exposedForest,exposedConfig,frontReads,frontCost,highKey,rightClean,rightMarked,
    exposed,targetErases,ids,exposedRep,exposedUnique,exposedAssembly,_,_,frontBound⟩ :=
    PreparedExposureExecution.sentinel reference preferences d valid terminal upper component represented color decorated erases logicalUnique
      forest forestRep physicalUnique headerKey payload config assembled
  obtain ⟨highId,terminalId,taggedTail,targetEq,tailEq⟩ :=
    IdentifiedBoundaryViews.sentinel target high (terminalLeaf d).rootRecord d right.tree targetErases
  have targetUnique : (target.inventory Prod.fst).Nodup := by rw [ids]; exact logicalUnique
  rw [targetEq] at exposed exposedRep targetUnique
  obtain ⟨finalForest,finalConfig,reads,cost,actual,finalRep,finalUnique,finalAssembly,wellFormed,bound⟩ :=
    ComponentBoundaryContinuation.sentinel (OpenSplitController.program d) .start .done decorated.rootRecord.1
      color (highId,high) (terminalId,(terminalLeaf d).rootRecord) d taggedTail targetUnique
      exposedForest exposedRep exposedUnique headerKey payload config exposedConfig exposed exposedAssembly
  exact ⟨right,high,highId,terminalId,taggedTail,finalForest,finalConfig,reads,cost,
    highKey,rightClean,rightMarked,tailEq,actual,finalRep,finalUnique,finalAssembly,wellFormed,by omega⟩

end ChaCha.Paper20261030.SecondaryDecomposition.ObservedPreparedExposure
