import TangoSquared.Paper20261030.LocalComponentEndpoint
import TangoSquared.Paper20261030.PrimaryHeaderProgram

/-! AccessExit driven by an original key and locally read component data.
The program reads the reached header, computes the exit from its bottom
key, performs all secondary repairs, and reaches the attached primary
payload. No exit depth or logical root identifier is supplied at runtime.

The initial representation must contain a correct header and already
positioned component fingers. This theorem does not yet implement
SwitchHead or maintain the header's cached root identifier for a later
component access.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.OriginalAccessController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler ComponentEndpointController

variable {β ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev Record (ι η C : Type*) := PrimaryHeaderController.Record (List (Option (Datum ι η C))) η
abbrev ControllerState (ι η C : Type*) :=
  PrimaryHeaderController.State (ComponentEndpointController.ControllerState ι η C) C (List (Option (Datum ι η C))) η

def program (height : Nat) (request : Int) (virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (ControllerState ι η C) C (Record ι η C) :=
  PrimaryHeaderController.program height request virtualColor (fun header => ComponentEndpointController.initial header.rootId)
    (fun depth => ComponentEndpointController.program depth virtualColor orientation)

def Exposes (config : MultiSourceProgram.Configuration C β (Record ι η C)) (q : C)
    (payload : Source β (List (Option (Datum ι η C)))) : Prop :=
  ∃ position, ∃ current : Cursor β (Record ι η C), ∃ routing : List (Datum ι η C),
    config.fingers q = some position ∧ SourcePositions.locate config.tree position = some current ∧
    current.focus.mapRecords Prod.fst = payload.setRoot (routing.map some ++ none::payload.rootRecord)

theorem exposes_lift (config : MultiSourceProgram.Configuration C β (Record ι η C)) (q : C)
    (payload : Source β (List (Option (Datum ι η C))))
    (exposed : ComponentEndpointController.Exposes (config.mapRecords Prod.fst) q payload) :
    Exposes config q payload := by
  obtain ⟨position,outside,routing,present,reached⟩ := exposed
  obtain ⟨actual,found,same⟩ := SourcePositions.lift_locate Prod.fst config.tree position _ reached
  exact ⟨position,actual,routing,present,found,congrArg Cursor.focus same⟩

theorem access {a b H : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Int) (header : PrimaryHeaderController.Header η)
    (validRequest : Dyadic.ValidKey H request) (validBottom : Dyadic.ValidKey H header.bottom)
    (valid : a ≤ Dyadic.lcaDepth H request header.bottom ∧ Dyadic.lcaDepth H request header.bottom ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → C) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup) (rootId : header.rootId = decorated.rootRecord.1)
    (forest : TaggedForest C Nat (LogicalRecord η C) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (virtualColor : C) (realColor : color (Dyadic.lcaDepth H request header.bottom) ≠ virtualColor)
    (orientation : C → Bool) (headerKey : Nat)
    (payload : C → Nat → Source β (List (Option (Datum ι η C))))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (Record ι η C))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout =
      some (config.mapRecords Prod.fst))
    (position : List Bool) (current : Cursor β (Record ι η C))
    (present : config.fingers virtualColor = some position)
    (reached : SourcePositions.locate config.tree position = some current)
    (stored : current.focus.rootRecord.2 = some header) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Cursor Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate (Dyadic.lcaDepth H request header.bottom) preferences)) out ∧
      target.tree.mapRecords Prod.snd = closed out ∧
      target.tree.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Run (program H request virtualColor orientation) .start config
        (.running header (.ready (ComponentEndpointController.finalState target.focus.rootRecord.1))) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout =
        some (finalConfig.mapRecords Prod.fst) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      Exposes finalConfig (color (Dyadic.lcaDepth H request header.bottom))
        (payload (color (Dyadic.lcaDepth H request header.bottom)) (Dyadic.lcaDepth H request header.bottom)) ∧
      finalConfig.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧
      cost ≤ 2*((118560*(Fintype.card C+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips (Dyadic.lcaDepth H request header.bottom)+1)*
          EndpointController.bound reference))+1 := by
  obtain ⟨out,target,finalForest,plainFinal,plainReads,plainCost,outRep,targetErases,inventory,plainRun,
      finalRep,finalUnique,finalAssembled,wellFormed,exposed,bounded⟩ :=
    ComponentEndpointController.access reference preferences (Dyadic.lcaDepth H request header.bottom) valid component
      represented color decorated erases logicalUnique forest forestRep physicalUnique virtualColor realColor orientation
      headerKey payload layout distinct covers (config.mapRecords Prod.fst) assembled
  rw [← rootId] at plainRun
  obtain ⟨finalConfig,reads,cost,actual,finalErases,metadata,costBound⟩ :=
    PrimaryHeaderController.dispatch H request virtualColor (fun header => ComponentEndpointController.initial header.rootId)
      (fun depth => ComponentEndpointController.program depth virtualColor orientation)
      config position current present reached header stored validRequest validBottom plainRun
  rw [← finalErases] at finalAssembled wellFormed exposed
  exact ⟨out,target,finalForest,finalConfig,reads,cost,outRep,targetErases,inventory,actual,finalRep,finalUnique,
    finalAssembled,wellFormed.of_mapRecords Prod.fst,exposes_lift finalConfig _ _ exposed,metadata,
    costBound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bounded) 1)⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.OriginalAccessController
