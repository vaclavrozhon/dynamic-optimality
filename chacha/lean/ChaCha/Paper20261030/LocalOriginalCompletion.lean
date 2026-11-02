import ChaCha.Paper20261030.LocalOriginalEntryAccess
import ChaCha.Paper20261030.LocalComponentSecondaryAccess
import ChaCha.Paper20261030.ComponentLeafService
import ChaCha.Paper20261030.MultiSourceMappedService

/-! The completion branch of an original-key component access.
If the request is the stored bottom key, its computed depth is H. After
the header read, charged entry, and full secondary update, an actual read
of the original key leaf certifies service in the shared-tree model.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.OriginalCompletionController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentAccessController ForestConnector.ThreeColors

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

variable {ι η : Type*} [DecidableEq ι] [DecidableEq η]

abbrev Record (ι η : Type*) := OriginalEntryController.Record ι η
abbrev AccessState (ι η : Type*) := PrimaryEntryController.State
  (ComponentAccessController.ControllerState ι η (Option Bool)) (Option (Datum ι η (Option Bool))) η

def accessProgram (height : Nat) (request : Int) :
    MultiSourceProgram.Program (AccessState ι η) (Option Bool) (Record ι η) :=
  PrimaryEntryController.program height request ComponentAccessController.initial
    (fun depth => ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation)

def program (height : Nat) (request : Int) :
    MultiSourceProgram.Program (Option (AccessState ι η)) (Option Bool) (Record ι η) :=
  ReadCompletionController.program (accessProgram height request) none

theorem access {a H : Nat} (reference : DepthTree a H) (preferences : DepthSplit → Bool)
    (request : Int) (header : PrimaryHeaderController.Header η)
    (validRequest : Dyadic.ValidKey H request) (completion : header.bottom = request) (valid : a ≤ H)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup) (rootId : header.rootId = decorated.rootRecord.1)
    (forest : TaggedForest (Option Bool) Nat (LogicalRecord η (Option Bool)) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (headerKey : Nat) (payload : Option Bool → Nat → Source Int (List (Option (Datum ι η (Option Bool)))))
    (extra : List (Option (Datum ι η (Option Bool)))) (payloadLeaf : payload none headerKey = .leaf request extra)
    (headerTree : Source Int (List (Option (Datum ι η (Option Bool)))))
    (headerPresent : representation none LocalComponentCompiler.wingOrientation headerKey payload forest none = some ⟨headerTree,[]⟩)
    (leftWing : header.leftWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some false)).isSome)
    (config : MultiSourceProgram.Configuration (Option Bool) Int (Record ι η))
    (entry : config.mapRecords Prod.fst = entryConfiguration
      (representation none LocalComponentCompiler.wingOrientation headerKey payload forest) headerTree)
    (stored : config.tree.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate H preferences)) out ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Serves (program H request) request (some .start) config none finalConfig reads cost ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest)
        (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
        some (finalConfig.mapRecords Prod.fst) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      finalConfig.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧
      cost ≤ 2*((118560*(Fintype.card (Option Bool)+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips H+1)*AccessController.bound reference))+12 := by
  let physical := representation none LocalComponentCompiler.wingOrientation headerKey payload forest
  have assembled := assemble_configuration physical ⟨headerTree,[]⟩ headerPresent
  obtain ⟨out,target,finalForest,plainFinal,plainReads,plainCost,outRep,targetErases,inventory,plainRun,
      finalRep,finalUnique,finalAssembled,wellFormed,bounded⟩ :=
    ComponentAccessController.access reference preferences H ⟨valid,le_rfl⟩ component represented color decorated erases
      logicalUnique forest forestRep physicalUnique none LocalComponentCompiler.wingOrientation headerKey payload
      (layout physical) (distinct physical) (covers physical) (configuration physical ⟨headerTree,[]⟩) assembled
  have validBottom : Dyadic.ValidKey H header.bottom := by simpa only [completion] using validRequest
  have lca : Dyadic.lcaDepth H request header.bottom = H := by
    rw [← Dyadic.exitDepth_eq_lcaDepth validRequest validBottom]
    exact (Dyadic.exitDepth_completion validRequest validBottom).mpr completion.symm
  have queried : MultiSourceProgram.Run
      (ComponentAccessController.program (Dyadic.lcaDepth H request header.bottom) none LocalComponentCompiler.wingOrientation)
      (ComponentAccessController.initial header.rootId) (configuration physical ⟨headerTree,[]⟩)
      (ComponentAccessController.finalState target.rootRecord.1) plainFinal plainReads plainCost := by
    simpa only [lca,rootId] using plainRun
  have rooted : ∀ q current, physical q = some current → current.ancestors = [] :=
    LocalComponentCompiler.representation_root color decorated forest forestRep none LocalComponentCompiler.wingOrientation headerKey payload
  obtain ⟨finalConfig,reads,cost,actual,finalErases,metadata,costBound⟩ :=
    PrimaryEntryController.dispatch H request ComponentAccessController.initial
      (fun depth => ComponentAccessController.program depth none LocalComponentCompiler.wingOrientation)
      physical headerTree rooted header leftWing rightWing config entry stored validRequest validBottom queried
  obtain ⟨records,headerAtLeaf⟩ := LocalComponentCompiler.header_leaf none LocalComponentCompiler.wingOrientation headerKey
    payload finalForest request extra payloadLeaf
  have member : none ∈ ForestConnector.colors (layout physical) := (covers physical) none _ headerPresent
  obtain ⟨position,outside,finger,reached⟩ := ForestConnector.assemble_cursor _ (layout physical) plainFinal finalAssembled
    none member ⟨.leaf request records,[]⟩ headerAtLeaf
  rw [← finalErases] at finger reached finalAssembled wellFormed
  obtain ⟨actualRecord,served⟩ := ReadCompletionController.serve_mapped (accessProgram H request) none actual Prod.fst request
    records position outside finger (by simpa only [MultiSourceProgram.Configuration.mapRecords,Cursor.extend,List.nil_append] using reached)
  refine ⟨out,target,finalForest,finalConfig,_,cost+1,outRep,targetErases,inventory,served,finalRep,finalUnique,
    finalAssembled,wellFormed.of_mapRecords Prod.fst,metadata,?_⟩
  have total := costBound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bounded) 11)
  omega

end ChaCha.Paper20261030.SecondaryDecomposition.OriginalCompletionController
