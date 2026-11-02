import ChaCha.Paper20261030.PrimaryHeaderRefresh
import ChaCha.Paper20261030.LocalPhysicalPacketStaging

set_option autoImplicit false

/-! Refreshing the cached logical root at an already reached component
root inside the global tree. This is one actual read and one write. It
preserves the entire payload configuration and every finger position. -/

namespace ChaCha.Paper20261030.PrimaryHeaderRefresh

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram PrimaryHeaderController

variable {α ρ η F : Type*} [DecidableEq F]

def refreshed (header : Header η) (freshId : η) (current : Cursor α (Record ρ η)) : Cursor α (Record ρ η) :=
  ⟨current.focus.setRoot (edit header freshId current.focus.rootRecord),current.ancestors⟩

theorem refreshed_erases (header : Header η) (freshId : η) (current : Cursor α (Record ρ η)) :
    (refreshed header freshId current).mapRecords Prod.fst = current.mapRecords Prod.fst := by
  obtain ⟨focus,outside⟩ := current
  cases focus <;> rfl

theorem refreshed_header (header : Header η) (freshId : η) (current : Cursor α (Record ρ η)) :
    (refreshed header freshId current).focus.rootRecord.2 = some {header with rootId := freshId} := by
  obtain ⟨focus,outside⟩ := current
  cases focus <;> rfl

theorem at_cursor (finger : F) (header : Header η) (freshId : η)
    (current : Cursor α (Record ρ η)) (config : Configuration F α (Record ρ η))
    (represented : MultiSourceSingleCursor.Represents finger current config) (valid : WellFormed config) :
    ∃ target reads,
      Run (program finger header freshId []) (some .reading) config (some .done) target reads 2 ∧
      target.mapRecords Prod.fst = config.mapRecords Prod.fst ∧
      MultiSourceSingleCursor.Represents finger (refreshed header freshId current) target ∧
      WellFormed target := by
  have sourceRun := RootRecordTour.edit_run (edit header freshId) current.focus current.ancestors
  obtain ⟨target,actual,targetRep,others⟩ := MultiSourceSingleCursor.compile_edge_run
    (RootRecordTour.program (edit header freshId) []) (RootRecordTour.edgeOnly _ _) finger sourceRun config represented
  have treeErases : target.tree.mapRecords Prod.fst = config.tree.mapRecords Prod.fst := by
    rw [targetRep.1,represented.1,← Cursor.mapRecords_tree,← Cursor.mapRecords_tree]
    exact congrArg Cursor.tree (refreshed_erases header freshId current)
  have fingers : target.fingers = config.fingers := by
    funext other
    by_cases same : other = finger
    · subst other
      exact targetRep.2.trans represented.2.symm
    · exact others other same
  refine ⟨target,_,actual,?_,targetRep,actual.wellFormed valid⟩
  simp only [Configuration.mapRecords,treeErases,fingers]

end ChaCha.Paper20261030.PrimaryHeaderRefresh
