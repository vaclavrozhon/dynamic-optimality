import ChaCha.Paper20261030.RootedComponentExecution
import ChaCha.Paper20261030.LocalPreparedRestore

set_option autoImplicit false

/-!
# Balanced restoration executed on the represented original-key component

The source restoration routines now run through the existing colored
compiler. Their endpoint is a canonical three-piece physical assembly
with reusable root positions, unique ids, unchanged wing presence, and
the prescribed secondary preferences. The payload subtrees are retained.
The theorem is for one component configuration; the complete primary
schedule must place the active and dormant executions in the shared tree.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage SourcePointer Structural PhysicalForestMetadata Auxiliary AuxiliaryComponent BoundaryObservations PathDecomposition
open LocalComponentForestCompiler LocalComponentCompiler ForestConnector.ThreeColors

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Logical (η : Type*) := LocalColoredCompiler.LogicalRecord Cached η (Option Bool)
abbrev Datum (ι η : Type*) := PhysicalDatum Nat Cached ι η (Option Bool)

def program (prefixPresent : Bool) :
    MultiSourceProgram.Program (State (HeadRestoreController.State Nat (DepthSplit × Bool)) Nat Cached ι η (Option Bool))
      (Option Bool) (List (Option (Datum ι η))) :=
  LocalComponentCompiler.program (HeadRestoreController.program prefixPresent) none wingOrientation

theorem sentinel {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (terminal : (Secondary.decodeDepth reference preferences).terminal = d)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (suffixSource reference preferences d valid) component)
    (found : searchResult d component.core = true)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd =
      .fork (component.core.size,⟨d,(splitAt d component.core component.balanced found).value⟩)
        (terminalLeaf d) (cutRight component d found).tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Equivalent out component ∧ Represents followsRight (suffixSource reference preferences d valid) out ∧
      MultiSourceProgram.Run (program false) (ready (HeadRestoreController.initial false) decorated.rootRecord.1)
        config (ready .done target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310) := by
  obtain ⟨out,equivalent,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedRestoreController.sentinel reference preferences d valid terminal component represented found []
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound⟩ :=
    RootedComponentExecution.compile_run (HeadRestoreController.program false) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled
  exact ⟨out,target,finalForest,finalConfig,reads,cost,equivalent,outRep,actual,targetErases,ids,finalRep,finalUnique,
    finalAssembly,presence,wellFormed,bound.trans (Nat.mul_le_mul_left _ sourceBound)⟩

theorem active {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (d : Nat) (valid : a ≤ d ∧ d ≤ b) (lower : a < d)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = d)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = d)
    (old incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (oldRep : Represents followsRight (source reference oldPreferences) old)
    (incomingRep : Represents followsRight (suffixSource reference incomingPreferences d valid) incoming)
    (lowFound : searchResult (d-1) old.core = true) (highFound : searchResult d incoming.core = true)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd =
      .fork (old.core.size,⟨d-1,(splitAt (d-1) old.core old.balanced lowFound).value⟩)
        (cutLeft old (d-1) lowFound).tree
        (.fork (incoming.core.size,⟨d,(splitAt d incoming.core incoming.balanced highFound).value⟩)
          (terminalLeaf d) (cutRight incoming d highFound).tree))
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.spliceBits d oldPreferences incomingPreferences)) out ∧
      MultiSourceProgram.Run (program true) (ready (HeadRestoreController.initial true) decorated.rootRecord.1)
        config (ready .done target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(6300*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+620) := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedRestoreController.active reference oldPreferences incomingPreferences d valid lower preparedOld preparedIncoming
      old incoming oldRep incomingRep lowFound highFound []
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound⟩ :=
    RootedComponentExecution.compile_run (HeadRestoreController.program true) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled
  exact ⟨out,target,finalForest,finalConfig,reads,cost,outRep,actual,targetErases,ids,finalRep,finalUnique,
    finalAssembly,presence,wellFormed,bound.trans (Nat.mul_le_mul_left _ sourceBound)⟩

theorem root_active {a b : Nat} (reference : DepthTree a b) (oldPreferences incomingPreferences : DepthSplit → Bool)
    (preparedOld : (Secondary.decodeDepth reference oldPreferences).terminal = a)
    (preparedIncoming : (Secondary.decodeDepth reference incomingPreferences).terminal = a)
    (incoming : AuxiliaryComponent Nat Nat (Tagged Payload))
    (incomingRep : Represents followsRight
      (suffixSource reference incomingPreferences a ⟨le_rfl,Secondary.reference_bounds reference⟩) incoming)
    (found : searchResult a incoming.core = true)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd =
      .fork (incoming.core.size,⟨a,(splitAt a incoming.core incoming.balanced found).value⟩)
        (terminalLeaf a) (cutRight incoming a found).tree)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest (Option Bool) Nat (Logical η) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) (headerKey : Nat)
    (payload : Option Bool → Nat → Source β (List (Option (Datum ι η))))
    (config : MultiSourceProgram.Configuration (Option Bool) β (List (Option (Datum ι η))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (layout (representation none wingOrientation headerKey payload forest)) = some config) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.spliceBits a oldPreferences incomingPreferences)) out ∧
      MultiSourceProgram.Run (program false) (ready (HeadRestoreController.initial false) decorated.rootRecord.1)
        config (ready .done target.rootRecord.1) finalConfig reads cost ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none wingOrientation headerKey payload finalForest)
        (layout (representation none wingOrientation headerKey payload finalForest)) = some finalConfig ∧
      (∀ q, (representation none wingOrientation headerKey payload finalForest q).isSome =
        (representation none wingOrientation headerKey payload forest q).isSome) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 474240*(2100*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+310) := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    PreparedRestoreController.root_active reference oldPreferences incomingPreferences preparedOld preparedIncoming incoming incomingRep found []
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,ids,finalRep,finalUnique,finalAssembly,presence,wellFormed,bound⟩ :=
    RootedComponentExecution.compile_run (HeadRestoreController.program false) color headerKey payload sourceRun
      decorated erases logicalUnique forest forestRep physicalUnique config assembled
  exact ⟨out,target,finalForest,finalConfig,reads,cost,outRep,actual,targetErases,ids,finalRep,finalUnique,
    finalAssembly,presence,wellFormed,bound.trans (Nat.mul_le_mul_left _ sourceBound)⟩

end ChaCha.Paper20261030.SecondaryDecomposition.PreparedRestoreExecution
