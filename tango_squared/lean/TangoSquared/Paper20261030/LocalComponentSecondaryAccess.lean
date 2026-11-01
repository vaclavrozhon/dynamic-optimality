import TangoSquared.Paper20261030.LocalComponentCompiler
import TangoSquared.Paper20261030.LocalSecondaryLeafService

/-! The complete secondary access loop as a local multifinger program
in one physical component tree, with mirrored routing wings, an explicit
header, and unchanged attached payloads. The initial connector/finger
configuration is a representation precondition. Its local construction,
the enclosing primary loop, and full workspace accounting are separate.
-/

namespace TangoSquared.Paper20261030.SecondaryDecomposition.ComponentAccessController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata
open LocalComponentForestCompiler

variable {β ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev ControllerState (ι η C : Type*) := State AccessController.State Nat Cached ι η C
abbrev LogicalRecord (η C : Type*) := LocalColoredCompiler.LogicalRecord Cached η C
abbrev Datum (ι η C : Type*) := PhysicalDatum Nat Cached ι η C

def program (request : Nat) (virtualColor : C) (orientation : C → Bool) :
    MultiSourceProgram.Program (ControllerState ι η C) C (List (Option (Datum ι η C))) :=
  LocalComponentCompiler.program (AccessController.program request) virtualColor orientation

def initial (id : η) : ControllerState ι η C := ready AccessController.initial id
def finalState (id : η) : ControllerState ι η C := ready (.done false) id

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
    (virtualColor : C) (orientation : C → Bool) (headerKey : Nat)
    (payload : C → Nat → Source β (List (Option (Datum ι η C))))
    (layout : Source C Unit) (distinct : (ForestConnector.colors layout).Nodup)
    (covers : ForestConnector.Covers layout (representation virtualColor orientation headerKey payload forest))
    (config : MultiSourceProgram.Configuration C β (List (Option (Datum ι η C))))
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some config) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)),
      ∃ finalForest finalConfig reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      target.mapRecords Prod.snd = closed out ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      MultiSourceProgram.Run (program request virtualColor orientation) (initial decorated.rootRecord.1) config
        (finalState target.rootRecord.1) finalConfig reads cost ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧
      ForestConnector.assemble (representation virtualColor orientation headerKey payload finalForest) layout = some finalConfig ∧
      MultiSourceProgram.WellFormed finalConfig ∧
      cost ≤ (118560*(Fintype.card C+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips request+1)*AccessController.bound reference) := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    AccessController.access reference preferences request valid component represented []
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor Nat Cached) = ⟨closed component,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,finalForest,finalConfig,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,finalRep,_,wellFormed,bounded⟩ :=
    LocalComponentCompiler.compile_run (AccessController.program request) color virtualColor orientation headerKey payload
      sourceRun ⟨decorated,[]⟩ cursorErases logicalUnique forest forestRep physicalUnique layout distinct covers config assembled
  have atRoot : target.ancestors = [] := by
    have equal := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using equal
  refine ⟨out,target.focus,finalForest,finalConfig,reads,cost,outRep,congrArg Cursor.focus targetErases,?_,actual,
    ?_,targetUnique,finalRep,wellFormed,?_⟩
  · simpa only [Cursor.tree,plug,atRoot] using inventory
  · simpa only [cursor,atRoot,frames,parentId] using targetRep
  · exact bounded.trans (Nat.mul_le_mul_left _ sourceBound)

end TangoSquared.Paper20261030.SecondaryDecomposition.ComponentAccessController
