import ChaCha.Paper20261030.LocalColoredCompiler
import ChaCha.Paper20261030.LocalSecondaryLeafService

/-! The complete secondary access loop executed in the physical color
forest. The program receives the requested depth and its current root id.
Every physical record observation, navigation, rotation, and write is
charged. The source's immutable identifiers and the physical pointer
annotations survive, so the representation can be reused for another
access. Placement into the primary original-key tree remains separate.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.ColoredAccessController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourcePointer Structural PhysicalForestMetadata

variable {ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev State (ι η C : Type*) := LocalColoredCompiler.State AccessController.State Cached ι η C
abbrev LogicalRecord (η C : Type*) := LocalColoredCompiler.LogicalRecord Cached η C

def program (request : Nat) : ForestLocalProgram.Program (State ι η C) C (Record (LogicalRecord η C) ι) :=
  LocalColoredCompiler.program (AccessController.program request)

def initial (id : η) : State ι η C := LocalColoredCompiler.ready AccessController.initial id
def finalState (id : η) : State ι η C := LocalColoredCompiler.ready (.done false) id

theorem access {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → C) (decorated : Source Nat (η × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (logicalUnique : (decorated.inventory Prod.fst).Nodup)
    (forest : TaggedForest C Nat (LogicalRecord η C) ι)
    (forestRep : ProjectionForest.Represents color ⟨annotate Prod.fst color none decorated,[]⟩ (erase forest))
    (physicalUnique : Unique forest) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (η × Cached)), ∃ finalForest reads cost,
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      target.mapRecords Prod.snd = closed out ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      ForestLocalProgram.Run (program request) (initial decorated.rootRecord.1) (encode forest)
        (finalState target.rootRecord.1) (encode finalForest) reads cost ∧
      ProjectionForest.Represents color ⟨annotate Prod.fst color none target,[]⟩ (erase finalForest) ∧
      Unique finalForest ∧ cost ≤ (29640*(Fintype.card C+1))*
        (((Secondary.decodeDepth reference preferences).accessFlips request+1)*AccessController.bound reference) := by
  obtain ⟨out,outRep,sourceReads,sourceCost,sourceRun,sourceBound⟩ :=
    AccessController.access reference preferences request valid component represented []
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor Nat Cached) = ⟨closed component,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,finalForest,reads,cost,actual,targetErases,inventory,targetRep,targetUnique,bounded⟩ :=
    LocalColoredCompiler.compile_run (AccessController.program request) color sourceRun
      ⟨decorated,[]⟩ cursorErases logicalUnique forest forestRep physicalUnique
  have atRoot : target.ancestors = [] := by
    have equal := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using equal
  refine ⟨out,target.focus,finalForest,reads,cost,outRep,congrArg Cursor.focus targetErases,?_,actual,?_,targetUnique,?_⟩
  · simpa only [Cursor.tree,plug,atRoot] using inventory
  · simpa only [cursor,atRoot,frames,parentId] using targetRep
  · exact bounded.trans (Nat.mul_le_mul_left _ sourceBound)

end ChaCha.Paper20261030.SecondaryDecomposition.ColoredAccessController
