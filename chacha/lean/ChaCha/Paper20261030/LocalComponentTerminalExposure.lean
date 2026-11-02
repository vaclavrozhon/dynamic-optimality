import ChaCha.Paper20261030.LocalComponentEndpoint
import ChaCha.Paper20261030.LocalTaggedComponentCompiler
import ChaCha.Paper20261030.ImmutableReadOnlyRun

/-! Terminal exposure after an already completed secondary access.
Unlike a fresh secondary access, this traversal preserves the entire
logical tree including its immutable identifiers. In particular the
cached root identifier remains the one obtained before exposure.
-/

namespace ChaCha.Paper20261030.BoundaryObservations.PortExposureController

theorem readonly {β : Nat → Type*} (request : Nat) : ImmutableSource.ReadOnly (program (β := β) request) := by
  intro state
  cases state with
  | search | done => trivial
  | down right => cases right <;> trivial

end ChaCha.Paper20261030.BoundaryObservations.PortExposureController

namespace ChaCha.Paper20261030.SecondaryDecomposition.ComponentTerminalController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {β ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev ControllerState (ι η C : Type*) := State PortExposureController.State Nat Cached ι η C
abbrev LogicalRecord (η C : Type*) := LocalColoredCompiler.LogicalRecord Cached η C
abbrev Datum (ι η C : Type*) := PhysicalDatum Nat Cached ι η C

def program (request : Nat) (virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (ControllerState ι η C) C (List (Option (Datum ι η C))) :=
  LocalComponentCompiler.program (PortExposureController.program request) virtualColor orientation

def initial (id : η) : ControllerState ι η C := ready (.search true) id
def finalState (id : η) : ControllerState ι η C := ready .done id

theorem expose {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (terminal : (Secondary.decodeDepth reference preferences).terminal = request)
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
    ∃ (target : Cursor Nat (η × Cached)), ∃ finalForest finalConfig reads cost,
      target.tree = decorated ∧
      MultiSourceProgram.Run (program request virtualColor orientation) (initial decorated.rootRecord.1) config
        (finalState target.focus.rootRecord.1) finalConfig reads cost ∧
      ProjectionForest.Represents color (cursor Prod.fst color target) (erase finalForest) ∧ Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      ForestConnector.Covers layout (representation virtualColor orientation headerKey payload finalForest) ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      ComponentEndpointController.Exposes finalConfig (color request) (payload (color request) request) ∧
      cost ≤ (59280*(Fintype.card C+1))*(6*Nat.clog 2 ((LocalReferences.depthReference reference).height+1)+1) := by
  obtain ⟨context,sourceReads,sourceCost,sourceRun,whole,sourceBound⟩ :=
    PortExposureController.expose_terminal reference preferences request terminal component represented []
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor Nat Cached) = ⟨closed component,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,taggedReads,taggedRun,targetErases,sameTree⟩ := ImmutableSource.readonly_run
    (PortExposureController.program request) (PortExposureController.readonly request) sourceRun ⟨decorated,[]⟩ cursorErases
  obtain ⟨finalForest,finalConfig,reads,cost,actual,finalRep,finalUnique,finalAssembled,finalCovered,valid,bounded⟩ :=
    LocalComponentCompiler.compile_tagged_run (PortExposureController.program request) color virtualColor orientation headerKey payload
      taggedRun logicalUnique forest forestRep physicalUnique layout distinct covers config assembled
  have leafErases := congrArg Cursor.focus targetErases
  have targetLeaf : target.focus = .leaf request target.focus.rootRecord := by
    cases focus : target.focus with
    | leaf key record =>
      have equal : key = request := (show key = request ∧ record.2 = (terminalLeaf request).rootRecord from by
        simpa only [Cursor.mapRecords,focus,Source.mapRecords,terminalLeaf,Source.leaf.injEq,Source.rootRecord] using leafErases).1
      simp only [equal,Source.rootRecord]
    | fork record left right => simp only [Cursor.mapRecords,focus,Source.mapRecords,terminalLeaf,reduceCtorEq] at leafErases
  obtain ⟨physical,routing,present,focus⟩ := LocalComponentCompiler.real_payload_focus color target request target.focus.rootRecord
    targetLeaf finalForest finalRep virtualColor realColor orientation headerKey payload
  obtain ⟨position,outside,finger,reached⟩ := ForestConnector.assemble_cursor _ layout finalConfig finalAssembled
    (color request) (finalCovered _ _ present) physical present
  refine ⟨target,finalForest,finalConfig,reads,cost,sameTree,actual,finalRep,finalUnique,finalAssembled,finalCovered,valid,?_,?_⟩
  · refine ⟨position,physical.ancestors++outside,routing,finger,?_⟩
    simpa only [Cursor.extend,focus] using reached
  · have size := represented_size reference preferences component represented
    have logBound := Nat.clog_monotone 2 (Nat.add_le_add_right size 1)
    exact bounded.trans (Nat.mul_le_mul_left _ (by omega))

end ChaCha.Paper20261030.SecondaryDecomposition.ComponentTerminalController
