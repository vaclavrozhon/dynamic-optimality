import TangoSquared.Paper20261030.LocalComponentOriginalAccess
import TangoSquared.Paper20261030.PrimaryEntryProgram
import TangoSquared.Paper20261030.ComponentRootPositions
import TangoSquared.Paper20261030.ComponentOriginalKeys

/-! An original-key AccessExit from the physical component root.
The root read obtains the bottom, logical root identifier, and wing bits.
The program then positions the three component fingers, updates all
secondary preferences, and exposes the primary-exit payload.

Used registers must initially be at the component root and unused ones
absent. The initial header is required to be correct. Reestablishing
these conditions after SwitchHead is still a separate obligation.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.OriginalEntryController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentEndpointController ForestConnector.ThreeColors

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

variable {β ι η : Type*} [DecidableEq ι] [DecidableEq η]

abbrev Record (ι η : Type*) := OriginalAccessController.Record ι η (Option Bool)
abbrev ControllerState (ι η : Type*) := PrimaryEntryController.State
  (ComponentEndpointController.ControllerState ι η (Option Bool)) (Option (Datum ι η (Option Bool))) η

def program (height : Nat) (request : Int) :
    MultiSourceProgram.Program (ControllerState ι η) (Option Bool) (Record ι η) :=
  PrimaryEntryController.program height request ComponentEndpointController.initial
    (fun depth => ComponentEndpointController.program depth none LocalComponentCompiler.wingOrientation)

theorem access {a b H : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Int) (header : PrimaryHeaderController.Header η)
    (validRequest : Dyadic.ValidKey H request) (validBottom : Dyadic.ValidKey H header.bottom)
    (valid : a ≤ Dyadic.lcaDepth H request header.bottom ∧ Dyadic.lcaDepth H request header.bottom ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → Option Bool) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup) (rootId : header.rootId = decorated.rootRecord.1)
    (forest : TaggedForest (Option Bool) Nat (LogicalRecord η (Option Bool)) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (realColor : color (Dyadic.lcaDepth H request header.bottom) ≠ none)
    (headerKey : Nat) (payload : Option Bool → Nat → Source β (List (Option (Datum ι η (Option Bool)))))
    (headerTree : Source β (List (Option (Datum ι η (Option Bool)))))
    (headerPresent : representation none LocalComponentCompiler.wingOrientation headerKey payload forest none = some ⟨headerTree,[]⟩)
    (leftWing : header.leftWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some true)).isSome)
    (rightWing : header.rightWing = (representation none LocalComponentCompiler.wingOrientation headerKey payload forest (some false)).isSome)
    (config : MultiSourceProgram.Configuration (Option Bool) β (Record ι η))
    (entry : config.mapRecords Prod.fst = entryConfiguration
      (representation none LocalComponentCompiler.wingOrientation headerKey payload forest) headerTree)
    (stored : config.tree.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Cursor Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate (Dyadic.lcaDepth H request header.bottom) preferences)) out ∧
      target.tree.mapRecords Prod.snd = closed out ∧
      target.tree.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Run (program H request) .start config
        (.running header (.ready (.running (ComponentEndpointController.finalState target.focus.rootRecord.1)))) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation none LocalComponentCompiler.wingOrientation headerKey payload finalForest)
        (layout (representation none LocalComponentCompiler.wingOrientation headerKey payload forest)) =
        some (finalConfig.mapRecords Prod.fst) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      OriginalAccessController.Exposes finalConfig (color (Dyadic.lcaDepth H request header.bottom))
        (payload (color (Dyadic.lcaDepth H request header.bottom)) (Dyadic.lcaDepth H request header.bottom)) ∧
      finalConfig.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧
      cost ≤ 2*((118560*(Fintype.card (Option Bool)+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips (Dyadic.lcaDepth H request header.bottom)+1)*
          EndpointController.bound reference))+11 := by
  let physical := representation none LocalComponentCompiler.wingOrientation headerKey payload forest
  have assembled := assemble_configuration physical ⟨headerTree,[]⟩ headerPresent
  obtain ⟨out,target,finalForest,plainFinal,plainReads,plainCost,outRep,targetErases,inventory,plainRun,
      finalRep,finalUnique,finalAssembled,wellFormed,exposed,bounded⟩ :=
    ComponentEndpointController.access reference preferences (Dyadic.lcaDepth H request header.bottom) valid component
      represented color decorated erases logicalUnique forest forestRep physicalUnique none realColor
      LocalComponentCompiler.wingOrientation headerKey payload (layout physical) (distinct physical) (covers physical)
      (configuration physical ⟨headerTree,[]⟩) assembled
  rw [← rootId] at plainRun
  have rooted : ∀ q current, physical q = some current → current.ancestors = [] :=
    LocalComponentCompiler.representation_root color decorated forest forestRep none LocalComponentCompiler.wingOrientation headerKey payload
  obtain ⟨finalConfig,reads,cost,actual,finalErases,metadata,costBound⟩ :=
    PrimaryEntryController.dispatch H request ComponentEndpointController.initial
      (fun depth => ComponentEndpointController.program depth none LocalComponentCompiler.wingOrientation)
      physical headerTree rooted header leftWing rightWing config entry stored validRequest validBottom plainRun
  rw [← finalErases] at finalAssembled wellFormed exposed
  exact ⟨out,target,finalForest,finalConfig,reads,cost,outRep,targetErases,inventory,actual,finalRep,finalUnique,
    finalAssembled,wellFormed.of_mapRecords Prod.fst,OriginalAccessController.exposes_lift finalConfig _ _ exposed,metadata,
    costBound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bounded) 11)⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.OriginalEntryController
