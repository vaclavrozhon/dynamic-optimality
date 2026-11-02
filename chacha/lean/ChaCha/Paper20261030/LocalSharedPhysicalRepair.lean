import ChaCha.Paper20261030.LocalPhysicalContextSpace
import ChaCha.Paper20261030.MultiSourceStationaryFingers

/-! The finite physical metadata repair in a shared tree, with every
physical finger restored to its exact initial address. Only reached
records are changed. The same constant cost holds in an arbitrary outer
context and with arbitrary additional valid fingers.
-/

namespace ChaCha.Paper20261030.PhysicalContextRepair

open ColoredStorage SourcePointer SourceLocalProgram Structural
open PhysicalBoundaryRepair (Record)

variable {κ α ρ ι F : Type*} [DecidableEq F]

theorem edgeOnly (identifier : ρ → ι) : MultiSourceSingleCursor.EdgeOnly (program (κ := κ) identifier) := by
  intro state action next instruction
  cases state with
  | ready tasks => cases tasks with
    | nil => simp only [program,reduceCtorEq] at instruction
    | cons task rest => cases task with
      | move edge =>
        cases edge <;> simp only [program,Edge.move,Instruction.nav.injEq] at instruction
        all_goals rcases instruction with ⟨rfl,_⟩; trivial
      | visit shape parent => simp only [program,PhysicalBoundaryRepair.program,Instruction.mapState,reduceCtorEq] at instruction
  | running shape parent tasks phase =>
    cases phase <;> simp only [program,PhysicalBoundaryRepair.program,Instruction.mapState,
      reduceCtorEq,Instruction.nav.injEq] at instruction
    all_goals rcases instruction with ⟨rfl,_⟩; trivial

def sharedProgram (identifier : ρ → ι) (finger : F) :
    MultiSourceProgram.Program (Option (State κ ρ ι)) F (Record ρ ι) :=
  MultiSourceSingleCursor.program (program identifier) finger

theorem shared (identifier : ρ → ι) (finger : F) (blocks : κ → Source α ρ) (parents : κ → Option ι)
    (context : Source κ (Record ρ ι)) (parent : Option ι) (outside)
    (config : MultiSourceProgram.Configuration F α (Record ρ ι))
    (represented : MultiSourceSingleCursor.Represents finger ⟨input identifier blocks parents context,outside⟩ config)
    (valid : MultiSourceProgram.WellFormed config) :
    ∃ target reads,
      MultiSourceProgram.Run (sharedProgram identifier finger)
        (some (.ready [.visit (context.mapRecords (fun _ => ())) parent])) config (some (.ready [])) target reads (cost context) ∧
      MultiSourceSingleCursor.Represents finger
        ⟨annotate identifier (fun _ => (() : Unit)) parent (plain blocks context),outside⟩ target ∧
      MultiSourceProgram.WellFormed target ∧ target.fingers = config.fingers := by
  obtain ⟨sourceReads,sourceRun⟩ := run identifier blocks parents context parent outside
  obtain ⟨target,actual,targetRep,otherFixed⟩ :=
    MultiSourceSingleCursor.compile_edge_run (program identifier) (edgeOnly identifier) finger sourceRun config represented
  refine ⟨target,_,actual,targetRep,actual.wellFormed valid,?_⟩
  funext other
  by_cases same : other = finger
  · subst other
    exact targetRep.2.trans represented.2.symm
  · exact otherFixed other same

end ChaCha.Paper20261030.PhysicalContextRepair
