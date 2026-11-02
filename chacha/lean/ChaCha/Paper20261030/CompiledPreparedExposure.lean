import ChaCha.Paper20261030.LocalPreparedExposure
import ChaCha.Paper20261030.RootedComponentExecution

set_option autoImplicit false

/-!
# Boundary preparation in the represented original-key component

Prepared secondary endpoints determine the successful split searches.
The actual colored compilation exposes the boundary while keeping the
component forest, physical assembly, unique ids, and unchanged payloads.
The exact tagged output is available to the canonical head-input proof.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedExposureExecution

open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (η : Type*) := LocalColoredCompiler.LogicalRecord Cached η (Option Bool)
abbrev Datum (ι η : Type*) := PhysicalDatum Nat Cached ι η (Option Bool)

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
    ∃ (left right : AuxiliaryComponent Nat Nat (Tagged Payload)) (low high : Cached) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      low.2.1 = d-1 ∧ high.2.1 = d ∧ Clean left.core ∧ MarkedPorts left ∧ Clean right.core ∧ MarkedPorts right ∧
      MultiSourceProgram.Run (LocalComponentCompiler.program (AdjacentExposureController.program (d-1)) none wingOrientation)
        (ready (.first .start) decorated.rootRecord.1) config (ready .done target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = .fork low left.tree (.fork high (terminalLeaf d) right.tree) ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(80220*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+4) := by
  obtain ⟨left,right,low,high,lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,_,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedExposureController.active reference preferences d terminal lower upper component represented []
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound⟩ :=
    RootedComponentExecution.compile_run (AdjacentExposureController.program (d-1)) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled
  exact ⟨left,right,low,high,target,finalForest,finalConfig,reads,cost,lowKey,highKey,leftClean,leftMarked,rightClean,rightMarked,
    actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound.trans (Nat.mul_le_mul_left _ sourceBound)⟩

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
    ∃ (right : AuxiliaryComponent Nat Nat (Tagged Payload)) (high : Cached) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      high.2.1 = d ∧ Clean right.core ∧ MarkedPorts right ∧
      MultiSourceProgram.Run (LocalComponentCompiler.program (OpenSplitController.program d) none wingOrientation)
        (ready .start decorated.rootRecord.1) config (ready .done target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = .fork high (terminalLeaf d) right.tree ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(40110*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+2) := by
  obtain ⟨right,high,highKey,rightClean,rightMarked,_,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedExposureController.sentinel reference preferences d valid terminal upper component represented []
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound⟩ :=
    RootedComponentExecution.compile_run (OpenSplitController.program d) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled
  exact ⟨right,high,target,finalForest,finalConfig,reads,cost,highKey,rightClean,rightMarked,
    actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound.trans (Nat.mul_le_mul_left _ sourceBound)⟩

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedExposureExecution
