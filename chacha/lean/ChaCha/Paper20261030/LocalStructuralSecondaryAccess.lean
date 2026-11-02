import ChaCha.Paper20261030.ImmutableStructuralCompiler
import ChaCha.Paper20261030.LocalSecondaryLeafService

/-! The complete secondary loop with immutable identifiers and structural
metadata, ready for the manuscript's fixed-color projection simulator.
The output retains the input identifiers, so successive accesses reuse
the same stored representation. The program depends only on the request.
Initializing or physically projecting this representation is separate.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition.StructuralAccessController

open ColoredStorage Auxiliary BoundaryObservations PathDecomposition SourceLocalProgram Structural

variable {ι C : Type*} [DecidableEq ι] [DecidableEq C]

abbrev State (ι C : Type*) := ImmutableStructural.State AccessController.State Cached ι C

def program (request : Nat) : Program (State ι C) ((ι × Cached) × Fields ι C) :=
  ImmutableStructural.program (AccessController.program request)

def initial : State ι C := ImmutableStructural.ready AccessController.initial

def finalState : State ι C := ImmutableStructural.ready (.done false)

theorem access {a b : Nat} (reference : DepthTree a b) (preferences : DepthSplit → Bool)
    (request : Nat) (valid : a ≤ request ∧ request ≤ b)
    (component : AuxiliaryComponent Nat Nat (Tagged Payload))
    (represented : Represents followsRight (source reference preferences) component)
    (color : Nat → C) (decorated : Source Nat (ι × Cached))
    (erases : decorated.mapRecords Prod.snd = closed component)
    (unique : (decorated.inventory Prod.fst).Nodup) :
    ∃ (out : AuxiliaryComponent Nat Nat (Tagged Payload)) (target : Source Nat (ι × Cached)),
      Represents followsRight (source reference (Secondary.intervalUpdate request preferences)) out ∧
      target.mapRecords Prod.snd = closed out ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧
      (∃ reads cost, Run (program request) initial ⟨annotate Prod.fst color none decorated,[]⟩
        finalState ⟨annotate Prod.fst color none target,[]⟩ reads cost ∧
        cost ≤ 38*(((Secondary.decodeDepth reference preferences).accessFlips request+1)*AccessController.bound reference)) ∧
      SourcePointer.VisitsLeaf request (annotate Prod.fst color none decorated) (annotate Prod.fst color none target)
        (38*(((Secondary.decodeDepth reference preferences).accessFlips request+1)*AccessController.bound reference)) := by
  obtain ⟨out,outRep,reads,cost,run,costBound⟩ :=
    AccessController.access reference preferences request valid component represented []
  obtain ⟨target,actualReads,actualCost,actualRun,targetErases,inventory,bounded⟩ :=
    ImmutableStructural.compile_root_run_on (AccessController.program request) color run decorated erases unique
  have reached := ImmutableStructural.compile_root_leaf_read_on (AccessController.program request) color
    (AccessController.reads_request reference preferences request valid component represented []) decorated erases unique
  have total : actualCost ≤
      38*(((Secondary.decodeDepth reference preferences).accessFlips request+1)*AccessController.bound reference) := by omega
  refine ⟨out,target,outRep,targetErases,inventory,⟨actualReads,actualCost,actualRun,total⟩,?_⟩
  intro outside
  obtain ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,front,focus,back,equalCost⟩ :=
    (reached.extend outside).trace (actualRun.extend outside)
  refine ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,?_,focus,?_,by omega⟩
  · simpa only [SourcePointer.Cursor.extend,List.nil_append] using front
  · simpa only [SourcePointer.Cursor.extend,List.nil_append] using back

end ChaCha.Paper20261030.SecondaryDecomposition.StructuralAccessController
