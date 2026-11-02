import ChaCha.Paper20261030.LocalCachedComponentAccess
import ChaCha.Paper20261030.LocalOriginalCompletion

/-! Actual original-key service in the completion branch with reusable
physical registers and a correct final root cache. After the full cached
secondary update, one actual leaf read serves the requested bottom key.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.CachedCompletionController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentAccessController ForestConnector.ThreeColors

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

variable {ι η : Type*} [DecidableEq ι] [DecidableEq η]

abbrev Record (ι η : Type*) := CachedComponentController.Record ι η

def program (origin : Option Bool) (height : Nat) (request : Int) :
    MultiSourceProgram.Program (Option (CachedComponentController.ControllerState ι η)) (Option Bool) (Record ι η) :=
  ReadCompletionController.program (CachedComponentController.program origin height request) none

theorem access {a H : Nat} (reference : DepthTree a H) (preferences : DepthSplit → Bool)
    (origin : Option Bool) (request : Int) (header : PrimaryHeaderController.Header η)
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
    (validConfig : MultiSourceProgram.WellFormed config) (atRoot : config.fingers origin = some [])
    (tree : config.tree.mapRecords Prod.fst =
      (configuration (representation none LocalComponentCompiler.wingOrientation headerKey payload forest) ⟨headerTree,[]⟩).tree)
    (stored : config.tree.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalBits finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate H preferences)) out ∧
      target.mapRecords Prod.snd = closed out ∧ target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Serves (program origin H request) request
        (some (CachedComponentController.initial origin H request)) config none finalConfig reads cost ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest)
        (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
        some ((finalConfig.mask finalBits).mapRecords Prod.fst) ∧
      finalConfig.tree.rootRecord.2 = some {header with rootId := target.rootRecord.1} ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ 2*((118560*(Fintype.card (Option Bool)+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips H+1)*AccessController.bound reference))+22 := by
  have validBottom : Dyadic.ValidKey H header.bottom := by simpa only [completion] using validRequest
  have depthEq : Dyadic.lcaDepth H request header.bottom = H := by
    rw [← Dyadic.exitDepth_eq_lcaDepth validRequest validBottom]
    exact (Dyadic.exitDepth_completion validRequest validBottom).mpr completion.symm
  obtain ⟨out,target,finalForest,active,finalConfig,reads,cost,outRep,targetErases,inventory,actual,
      finalRep,finalUnique,finalAssembled,finalCovered,presence,correctHeader,finalValid,bound⟩ :=
    CachedComponentController.access reference preferences origin request header validRequest validBottom
      (by rw [depthEq]; exact ⟨valid,le_rfl⟩) component represented color decorated erases logicalUnique rootId forest forestRep physicalUnique
      headerKey payload headerTree headerPresent leftWing rightWing config validConfig atRoot tree stored
  obtain ⟨records,headerAtLeaf⟩ := LocalComponentCompiler.header_leaf none LocalComponentCompiler.wingOrientation headerKey
    payload finalForest request extra payloadLeaf
  obtain ⟨position,outside,finger,reached⟩ := ForestConnector.assemble_cursor _ _ _ finalAssembled
    none (finalCovered _ _ headerAtLeaf) ⟨.leaf request records,[]⟩ headerAtLeaf
  have actualFinger : finalConfig.fingers none = some position :=
    (MultiSourceProgram.mask_present active finalConfig none position finger).2
  obtain ⟨actualRecord,served⟩ := ReadCompletionController.serve_mapped
    (CachedComponentController.program origin H request) none actual Prod.fst request records position outside actualFinger
    (by simpa only [MultiSourceProgram.Configuration.mask,MultiSourceProgram.Configuration.mapRecords,Cursor.extend,List.nil_append] using reached)
  refine ⟨out,target,finalForest,active,finalConfig,_,cost+1,?_,targetErases,inventory,served,finalRep,
    finalUnique,finalAssembled,correctHeader,finalValid,?_⟩
  · simpa only [depthEq] using outRep
  · rw [depthEq] at bound
    omega

end ChaCha.Paper20261030.SecondaryDecomposition.CachedCompletionController
