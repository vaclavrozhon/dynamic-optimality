import TangoSquared.Paper20261030.LocalSecondaryEndpoint
import TangoSquared.Paper20261030.ComponentPayloadFocus
import TangoSquared.Paper20261030.ForestConnectorPositions

/-! The secondary repairs followed by actual primary-exit exposure in
one common physical tree. The program ends with the exit's color finger
at the attached payload root. Its original metadata remains after the
routing prefix and delimiter. The primary loop can continue there.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.ComponentEndpointController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {β ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev ControllerState (ι η C : Type*) := State EndpointController.State Nat Cached ι η C
abbrev LogicalRecord (η C : Type*) := LocalColoredCompiler.LogicalRecord Cached η C
abbrev Datum (ι η C : Type*) := PhysicalDatum Nat Cached ι η C

def program (request : Nat) (virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (ControllerState ι η C) C (List (Option (Datum ι η C))) :=
  LocalComponentCompiler.program (EndpointController.program request) virtualColor orientation

def initial (id : η) : ControllerState ι η C := ready EndpointController.initial id
def finalState (id : η) : ControllerState ι η C := ready EndpointController.finalState id

def Exposes (config : MultiSourceProgram.Configuration C β (List (Option (Datum ι η C))))
    (q : C) (payload : Source β (List (Option (Datum ι η C)))) : Prop :=
  ∃ position outside, ∃ (routing : List (Datum ι η C)),
    config.fingers q = some position ∧
    SourcePositions.locate config.tree position = some
      ⟨payload.setRoot (routing.map some ++ none::payload.rootRecord),outside⟩

theorem access {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → C) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest C Nat (LogicalRecord η C) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest)
    (virtualColor : C) (realColor : color request ≠ virtualColor) (orientation : C → Bool) (headerKey : Nat)
    (payload : C → Nat → Source β (List (Option (Datum ι η C))))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (Datum ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Cursor Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      target.tree.mapRecords Prod.snd = closed out ∧
      target.tree.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Run (program request virtualColor orientation) (initial decorated.rootRecord.1) config
        (finalState target.focus.rootRecord.1) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      Exposes finalConfig (color request) (payload (color request) request) ∧
      cost ≤ (118560*(Fintype.card C+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips request+1)*EndpointController.bound reference) := by
  obtain ⟨out,sourceContext,sourceReads,sourceCost,outRep,sourceRun,whole,sourceBound⟩ :=
    EndpointController.access reference preferences request valid component represented []
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor Nat Cached) = ⟨closed component,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,finalRep,finalCovers,wellFormed,bounded⟩ :=
    LocalComponentCompiler.compile_run (EndpointController.program request) color virtualColor orientation headerKey payload
      sourceRun ⟨decorated,[]⟩ cursorErases logicalUnique forest forestRep physicalUnique layout distinct covers config assembled
  have treeErases : target.tree.mapRecords Prod.snd = closed out := by
    rw [← Cursor.mapRecords_tree,targetErases]
    simpa only [Cursor.tree,plug] using whole
  have leafErases := congrArg Cursor.focus targetErases
  have targetLeaf : target.focus = .leaf request target.focus.rootRecord := by
    cases focus : target.focus with
    | leaf key record =>
      have equal : key = request := (show key = request ∧ record.2 = (terminalLeaf request).rootRecord from by
        simpa only [Cursor.mapRecords,focus,Source.mapRecords,terminalLeaf,Source.leaf.injEq,Source.rootRecord] using leafErases).1
      simp only [equal,Source.rootRecord]
    | fork record left right =>
      simp only [Cursor.mapRecords,focus,Source.mapRecords,terminalLeaf,reduceCtorEq] at leafErases
  obtain ⟨physical,routing,present,focus⟩ := LocalComponentCompiler.real_payload_focus color target request
    target.focus.rootRecord targetLeaf finalForest targetRep virtualColor realColor orientation headerKey payload
  obtain ⟨position,outside,finger,reached⟩ := ForestConnector.assemble_cursor _ layout finalConfig finalRep
    (color request) (finalCovers _ _ present) physical present
  refine ⟨out,target,finalForest,finalConfig,reads,cost,outRep,treeErases,inventory,actual,targetRep,targetUnique,
    finalRep,wellFormed,?_,bounded.trans (Nat.mul_le_mul_left _ sourceBound)⟩
  exact ⟨position,physical.ancestors++outside,routing,finger,by simpa only [Cursor.extend,focus] using reached⟩

end TangoSquared.Paper20261030.SecondaryDecomposition.ComponentEndpointController
