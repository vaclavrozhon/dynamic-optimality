import TangoSquared.Paper20261030.PackedRotationWriteLabels
import TangoSquared.Paper20261030.PackedSourceCompiler

set_option autoImplicit false

/-! Per-write physical-id preservation for the complete source-to-color
compiler. The strengthened execution follows the existing checked
metadata-ready source run and composes the same helper programs. -/
namespace TangoSquared.Paper20261030.PackedSourceCompiler

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata
open DynamicOptimality.LocalProgram (Move)

variable {α ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem child_steps_labels (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) (state next : σ) (right : Bool)
    (instruction : source state = .nav (if right then .right else .left) next)
    (l r : Source α (LogicalRecord ρ η C)) (record : LogicalRecord ρ η C) (outside)
    (children : PackedReadiness.Children identifier color (.fork record l r))
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color ⟨.fork record l r,outside⟩ (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : ((Cursor.tree ⟨.fork record l r,outside⟩).inventory (fun entry => identifier entry.1)).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program identifier source) (.ready state (identifier record.1)) (encode forest)
        (.ready next (identifier (PackedDescentController.child right l r record outside).focus.rootRecord.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color (PackedDescentController.child right l r record outside) (erase target) ∧
      Unique target ∧ cost ≤ 780*(Fintype.card C+1) := by
  obtain ⟨target,reads,cost,actual,targetRep,targetUnique,bounded⟩ :=
    PhysicalPackedChildController.descend_labels identifier color right l r record outside children forest represented physicalUnique
      (Multiset.inj_on_of_nodup_map logicalUnique)
  have positive : 0 < cost := by cases actual with | next => omega
  have mapped := actual.map_prefix (finishChild next (identifier record.1) right)
    (child_code identifier source next (identifier record.1) right)
  have changed := mapped.change_start (replacement := .ready state (identifier record.1)) positive (by
    cases right <;> simp [program,instruction,finishChild,PhysicalPackedChildController.initial,PackedChildController.initial])
  refine ⟨target,reads,cost,?_,targetRep,targetUnique,by omega⟩
  cases right <;> exact changed

theorem parent_steps_labels (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) (state next : σ) (right : Bool)
    (instruction : source state = .nav .up next)
    (l r : Source α (LogicalRecord ρ η C)) (record : LogicalRecord ρ η C) (outside)
    (ready : PackedReadiness.Parent identifier color (PackedDescentController.child right l r record outside))
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (PackedDescentController.child right l r record outside) (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : ((Cursor.tree ⟨.fork record l r,outside⟩).inventory (fun entry => identifier entry.1)).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program identifier source)
        (.ready state (identifier (PackedDescentController.child right l r record outside).focus.rootRecord.1)) (encode forest)
        (.ready next (identifier record.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨.fork record l r,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 780*(Fintype.card C+1) := by
  have fields : (PackedDescentController.child right l r record outside).focus.rootRecord.2.parent = some (identifier record.1) ∧
      ∃ leftId rightId, record.2.children = some
        (Child.mk leftId (l.support color),Child.mk rightId (r.support color)) := by
    cases right <;> exact ready
  obtain ⟨parentField,leftId,rightId,children⟩ := fields
  obtain ⟨target,reads,cost,actual,targetRep,targetUnique,bounded⟩ :=
    PhysicalPackedParentController.ascend_labels identifier color right l r record outside parentField children forest represented physicalUnique
      (Multiset.inj_on_of_nodup_map logicalUnique)
  have positive : 0 < cost := by cases actual with | next => omega
  let wanted := identifier (PackedDescentController.child right l r record outside).focus.rootRecord.1
  have mapped := actual.map_prefix (finishParent next wanted) (parent_code identifier source next wanted)
  have changed := mapped.change_start (replacement := .ready state wanted) positive (by
    simp only [program,instruction,finishParent,PhysicalPackedParentController.initial])
  exact ⟨target,reads,cost,changed,targetRep,targetUnique,by omega⟩

theorem rotation_steps_labels (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) (state next : σ) (right : Bool)
    (instruction : source state = .nav (if right then .rotateRight else .rotateLeft) next)
    (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) (outside)
    (ready : PackedReadiness.Rotation identifier color right ⟨PhysicalPackedRotation.before right u v w p top,outside⟩)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color ⟨PhysicalPackedRotation.before right u v w p top,outside⟩ (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : ((plug (PhysicalPackedRotation.before right u v w p top) outside).inventory (fun entry => identifier entry.1)).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program identifier source) (.ready state (identifier (PackedRotationProgram.firstRecord right p top).1)) (encode forest)
        (.ready next (identifier (PackedRotationProgram.secondRecord right p top).1)) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨PhysicalPackedRotation.after right u v w p top,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 780*(Fintype.card C+1) := by
  have fields : PackedRotationProgram.RootReady identifier color right u v w p top ∧
      PackedRotationProgram.PivotReady identifier color right u v w p top ∧
      (PackedRotationProgram.secondRecord right p top).2.parent = some (identifier (PackedRotationProgram.firstRecord right p top).1) ∧
      ColorsCorrect (fun record => record.2.colors) color (plug (PhysicalPackedRotation.before right u v w p top) outside) := by
    cases right <;> exact ready
  obtain ⟨rootReady,pivotReady,parentReady,correct⟩ := fields
  obtain ⟨target,reads,cost,actual,targetRep,targetUnique,bounded⟩ :=
    PackedRotationProgram.rotate_labels identifier color right u v w p top outside rootReady pivotReady parentReady correct forest physicalUnique logicalUnique represented
  have positive : 0 < cost := by cases actual with | next => omega
  let wanted := identifier (PackedRotationProgram.firstRecord right p top).1
  have mapped := actual.map_prefix (finishRotation next wanted right) (rotation_code identifier source next wanted right)
  have changed := mapped.change_start (replacement := .ready state wanted) positive (by
    cases right <;> simp [program,instruction,finishRotation,PackedRotationProgram.initial])
  refine ⟨target,reads,cost,?_,targetRep,targetUnique,by omega⟩
  cases right <;> exact changed

theorem nav_steps_labels (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) (state next : σ) (action : Move)
    (instruction : source state = .nav action next)
    (before after : Cursor α (LogicalRecord ρ η C)) (moved : SourceLocalProgram.navigate action before = some after)
    (ready : PackedReadiness.Ready identifier color (source state) before)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color before (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : (before.tree.inventory (fun entry => identifier entry.1)).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program identifier source) (.ready state (identifier before.focus.rootRecord.1)) (encode forest)
        (.ready next (identifier after.focus.rootRecord.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color after (erase target) ∧
      Unique target ∧ cost ≤ 780*(Fintype.card C+1) := by
  rw [instruction] at ready
  rcases before with ⟨focus,outside⟩
  cases action with
  | left => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork record l r =>
      cases Option.some.inj moved
      exact child_steps_labels identifier color source state next false instruction l r record outside ready forest represented physicalUnique logicalUnique
  | right => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork record l r =>
      cases Option.some.inj moved
      exact child_steps_labels identifier color source state next true instruction l r record outside ready forest represented physicalUnique logicalUnique
  | up => cases outside with
    | nil => simp [SourceLocalProgram.navigate] at moved
    | cons frame outside => cases frame with
      | left record r =>
        cases Option.some.inj moved
        exact parent_steps_labels identifier color source state next false instruction focus r record outside ready forest represented physicalUnique logicalUnique
      | right l record =>
        cases Option.some.inj moved
        exact parent_steps_labels identifier color source state next true instruction l focus record outside ready forest represented physicalUnique logicalUnique
  | rotateRight => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork top l w => cases l with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork p u v =>
        cases Option.some.inj moved
        exact rotation_steps_labels identifier color source state next true instruction u v w p top outside ready forest represented physicalUnique logicalUnique
  | rotateLeft => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork top v w =>
        cases Option.some.inj moved
        exact rotation_steps_labels identifier color source state next false instruction u v w p top outside ready forest represented physicalUnique logicalUnique

end TangoSquared.Paper20261030.PackedSourceCompiler

namespace TangoSquared.Paper20261030.PackedSourceCompiler

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem step_labels (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) {state next : σ}
    {before after : Cursor α (LogicalRecord ρ η C)} {entry}
    (execution : SourceLocalProgram.Step source state before next after entry)
    (ready : PackedReadiness.Ready identifier color (source state) before)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color before (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : (before.tree.inventory (fun (record : LogicalRecord ρ η C) => identifier record.1)).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Steps (fun record => record.1.1) (program identifier source) (.ready state (identifier before.focus.rootRecord.1)) (encode forest)
        (.ready next (identifier after.focus.rootRecord.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color after (erase target) ∧
      Unique target ∧ cost ≤ 780*(Fintype.card C+1) := by
  cases execution with
  | nav instruction moved =>
    exact nav_steps_labels identifier color source state next _ instruction before after moved ready forest represented physicalUnique logicalUnique
  | read instruction =>
    obtain ⟨reads,cost,actual,bounded⟩ := PhysicalRecordFinder.find_current
      (fun (record : LogicalRecord ρ η C) => identifier record.1) color before forest represented physicalUnique
      (Multiset.inj_on_of_nodup_map logicalUnique)
    have actual := PhysicalRecordFinder.write_labels _ _ actual
    have positive : 0 < cost := by cases actual with | next => omega
    let wanted := identifier before.focus.rootRecord.1
    have mapped := actual.map_prefix (finishRead identifier source state wanted) (read_code identifier source state wanted)
    have changed := mapped.change_start (replacement := .ready state wanted) positive (by
      simp only [program,instruction,finishRead])
    have leaf : before.focus.rootRecord.2.children.isNone = SourceLocalProgram.isLeaf before.focus := by
      simpa only [instruction,PackedReadiness.Ready] using ready
    refine ⟨forest,reads,cost,?_,represented,physicalUnique,by omega⟩
    simpa only [finishRead,instruction,leaf] using changed
  | write instruction =>
    rename_i fresh
    have same : identifier fresh.1 = identifier before.focus.rootRecord.1 := by
      simpa only [instruction,PackedReadiness.Ready] using ready
    obtain ⟨target,reads,cost,actual,targetRep,targetUnique,_,bounded⟩ :=
      PhysicalPackedWriteController.write_labels (fun (record : LogicalRecord ρ η C) => identifier record.1) color before fresh same forest represented physicalUnique logicalUnique
    have positive : 0 < cost := by cases actual with | next => omega
    let wanted := identifier before.focus.rootRecord.1
    have mapped := actual.map_prefix (finishWrite next wanted fresh) (write_code identifier source next wanted fresh)
    have changed := mapped.change_start (replacement := .ready state wanted) positive (by
      simp only [program,instruction,finishWrite])
    refine ⟨target,reads,cost,?_,targetRep,targetUnique,by omega⟩
    have root : (before.focus.setRoot fresh).rootRecord = fresh := by cases before.focus <;> rfl
    simpa only [root,same,finishWrite,wanted] using changed

theorem compile_write_labels (identifier : ρ → η) (color : α → C)
    (source : SourceLocalProgram.Program σ (LogicalRecord ρ η C)) {state last : σ}
    {before after : Cursor α (LogicalRecord ρ η C)} {readWord sourceCost}
    (execution : PackedReadiness.CheckedRun identifier color source state before last after readWord sourceCost)
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color before (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : (before.tree.inventory (fun (record : LogicalRecord ρ η C) => identifier record.1)).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program identifier source) (.ready state (identifier before.focus.rootRecord.1)) (encode forest)
        (.ready last (identifier after.focus.rootRecord.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color after (erase target) ∧
      Unique target ∧ cost ≤ (780*(Fintype.card C+1))*sourceCost := by
  induction execution generalizing forest with
  | halt stopped =>
    exact ⟨forest,[],0,.halt (by simp only [program,stopped]),represented,physicalUnique,by omega⟩
  | next first ready rest ih =>
    obtain ⟨middle,firstReads,firstCost,firstRun,middleRep,middleUnique,firstBound⟩ :=
      step_labels identifier color source first ready forest represented physicalUnique logicalUnique
    have middleLogical := logicalUnique
    rw [PackedReadiness.step_inventory identifier color first ready] at middleLogical
    obtain ⟨target,lastReads,lastCost,lastRun,targetRep,targetUnique,lastBound⟩ :=
      ih middle middleRep middleUnique middleLogical
    refine ⟨target,firstReads++lastReads,firstCost+lastCost,firstRun.then_run lastRun,targetRep,targetUnique,?_⟩
    rw [Nat.mul_add]
    omega

end TangoSquared.Paper20261030.PackedSourceCompiler
