import ChaCha.Paper20261030.PrimaryHeaderProgram
import ChaCha.Paper20261030.LocalRootRecordTour
import ChaCha.Paper20261030.MultiSourceStationaryFingers

/-! Local repair of the cached logical-root identifier. At a secondary
root boundary, the compiler already holds the new identifier in its state.
The header finger lies at depth at most two in the fixed component
connector. This controller visits that connector's root, updates only the
identifier in the previously loaded header, and returns, preserving all finger
positions and all routing data. Connecting this operation to the compiler's
root-boundary continuation is a separate composition step.
-/

namespace ChaCha.Paper20261030.RootRecordTour

theorem edgeOnly {ρ : Type*} (edit : ρ → ρ) (path : List Bool) :
    MultiSourceSingleCursor.EdgeOnly (program edit path) := by
  intro state move next instruction
  cases state with
  | ascending remaining => simp only [program,SourceLocalProgram.Instruction.nav.injEq] at instruction; cases instruction.1; trivial
  | reading => simp only [program,reduceCtorEq] at instruction
  | writing record => simp only [program,reduceCtorEq] at instruction
  | done => simp only [program,reduceCtorEq] at instruction
  | descending rest => cases rest with
    | nil => simp only [program,reduceCtorEq] at instruction
    | cons right rest => cases right <;>
      simp only [program,Bool.false_eq_true,if_false,if_true,SourceLocalProgram.Instruction.nav.injEq] at instruction <;>
      cases instruction.1 <;> trivial

end ChaCha.Paper20261030.RootRecordTour

namespace ChaCha.Paper20261030.PrimaryHeaderRefresh

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram PrimaryHeaderController

variable {α ρ η F : Type*} [DecidableEq F]

def edit (header : Header η) (freshId : η) (record : Record ρ η) : Record ρ η :=
  (record.1,some {header with rootId := freshId})

def program (finger : F) (header : Header η) (freshId : η) (path : List Bool) :
    Program (Option (RootRecordTour.State (Record ρ η))) F (Record ρ η) :=
  MultiSourceSingleCursor.program (RootRecordTour.program (edit header freshId) path) finger

theorem refresh (finger : F) (header : Header η) (freshId : η) (path : List Bool) (short : path.length ≤ 2)
    (config : Configuration F α (Record ρ η)) (current : Cursor α (Record ρ η))
    (present : config.fingers finger = some path) (reached : locate config.tree path = some current)
    (known : path = address current) (valid : WellFormed config) :
    ∃ target reads cost,
      Run (program finger header freshId path) (some (RootRecordTour.ascend path.length)) config
        (some .done) target reads cost ∧
      target.mapRecords Prod.fst = config.mapRecords Prod.fst ∧
      target.tree.rootRecord.2 = some {header with rootId := freshId} ∧
      WellFormed target ∧ cost ≤ 6 := by
  have initialRep : MultiSourceSingleCursor.Represents finger current config :=
    ⟨(locate_tree reached).symm,by simpa only [known] using present⟩
  obtain ⟨finalCursor,sourceRun,finalTree,erasedCursor⟩ :=
    RootRecordTour.run Prod.fst (edit header freshId) (fun _ => rfl) path current known
  obtain ⟨target,actual,targetRep,others⟩ := MultiSourceSingleCursor.compile_edge_run
    (RootRecordTour.program (edit header freshId) path) (RootRecordTour.edgeOnly _ _) finger sourceRun config initialRep
  have addressSame : address finalCursor = address current := by
    rw [← address_mapRecords Prod.fst finalCursor,erasedCursor,address_mapRecords]
  have fingersSame : target.fingers = config.fingers := by
    funext other
    by_cases same : other = finger
    · subst other
      exact targetRep.2.trans ((congrArg some addressSame).trans initialRep.2.symm)
    · exact others other same
  have erasedTree : target.tree.mapRecords Prod.fst = config.tree.mapRecords Prod.fst := by
    rw [targetRep.1,initialRep.1,← Cursor.mapRecords_tree,← Cursor.mapRecords_tree,erasedCursor]
  have correctHeader : target.tree.rootRecord.2 = some {header with rootId := freshId} := by
    rw [targetRep.1,finalTree,← initialRep.1]
    have root : (config.tree.setRoot (edit header freshId config.tree.rootRecord)).rootRecord = edit header freshId config.tree.rootRecord := by
      cases config.tree <;> rfl
    rw [root]
    rfl
  refine ⟨target,_,_,actual,?_,correctHeader,actual.wellFormed valid,by omega⟩
  simp only [Configuration.mapRecords,erasedTree,fingersSame]

end ChaCha.Paper20261030.PrimaryHeaderRefresh
