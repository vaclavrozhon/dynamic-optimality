import ChaCha.Paper20261030.PackedPhysicalWriteLabels
import ChaCha.Paper20261030.PhysicalFinderWriteLabels
import ChaCha.Paper20261030.LocalPackedRotation

set_option autoImplicit false

/-! Per-write physical-id preservation through parent lookup and the
complete read-driven packed rotation. All helper calls use the original
programs, with their original operation bounds. -/
namespace ChaCha.Paper20261030.PhysicalPackedParentController

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem ascend_labels [DecidableEq α] (identifier : ρ → η) (color : α → C) (right : Bool)
    (l r : Source α (LogicalRecord ρ η C)) (record : LogicalRecord ρ η C) (outside)
    (parentField : (PackedDescentController.child right l r record outside).focus.rootRecord.2.parent = some (identifier record.1))
    {leftId rightId : η}
    (children : record.2.children = some
      (Child.mk leftId (l.support color),Child.mk rightId (r.support color)))
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι)
    (represented : ProjectionForest.Represents color (PackedDescentController.child right l r record outside) (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : Distinguishes (fun entry => identifier entry.1) (Cursor.tree ⟨.fork record l r,outside⟩)) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program identifier (identifier (PackedDescentController.child right l r record outside).focus.rootRecord.1))
        initial (encode forest) (.done (identifier record.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨.fork record l r,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 48*Fintype.card C := by
  let current := PackedDescentController.child right l r record outside
  let wanted := identifier current.focus.rootRecord.1
  obtain ⟨readWord,readCost,readRun,readBound⟩ := PhysicalRecordFinder.find_current (fun entry => identifier entry.1)
    color current forest represented physicalUnique (by cases right <;> exact logicalUnique)
  have readRun := PhysicalRecordFinder.write_labels _ _ readRun
  have first := readRun.map_prefix finishRead (reading_code identifier wanted)
  change ForestWriteLabels.Steps (fun record => record.1.1) (program identifier wanted) initial (encode forest)
    (finishRead (.found current.focus.rootRecord)) (encode forest) readWord readCost at first
  have readEndpoint : finishRead (ρ := ρ) (ι := ι) (.found current.focus.rootRecord) =
      State.parent (identifier record.1) (.scan (Finset.univ.sort (· ≤ ·))) := by
    simp only [finishRead,parentField,current]
  rw [readEndpoint] at first
  obtain ⟨parentWord,parentCost,parentRun,parentBound⟩ := PhysicalRecordFinder.find_parent (fun entry => identifier entry.1)
    color right l r record outside forest represented physicalUnique logicalUnique
  have parentRun := PhysicalRecordFinder.write_labels _ _ parentRun
  have second := parentRun.map_prefix (finishParent (identifier record.1)) (parent_code identifier wanted (identifier record.1))
  obtain ⟨bare,moveRun,bareRep,moveBound⟩ := PackedAscentController.ascend color right l r record outside (erase forest) represented
  obtain ⟨target,moveWord,moveCost,compiled,targetErases,targetUnique,compiledBound⟩ :=
    PhysicalForestCompiler.compile_write_labels _ moveRun forest rfl physicalUnique
  have last := compiled.map_prefix (finishMove (identifier record.1)) (moving_code identifier wanted (identifier record.1))
  have parentEndpoint : finishParent (ρ := ρ) (ι := ι) (identifier record.1) (.found record) =
      finishMove (identifier record.1) (.ready ((l.support color ∩ r.support color).sort (· ≤ ·))) := by
    simp only [finishParent,children]
  rw [parentEndpoint] at second
  have whole := ((first.append second).append last).run rfl
  exact ⟨target,_,_,whole,by rw [targetErases]; exact bareRep,targetUnique,by omega⟩

end ChaCha.Paper20261030.PhysicalPackedParentController

namespace ChaCha.Paper20261030.PackedRotationProgram

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem rotate_labels [DecidableEq α] (identifier : ρ → η) (color : α → C) (right : Bool)
    (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) (outside : List (Frame α (LogicalRecord ρ η C)))
    (rootReady : RootReady identifier color right u v w p top)
    (pivotReady : PivotReady identifier color right u v w p top)
    (parentReady : (secondRecord right p top).2.parent = some (identifier (firstRecord right p top).1))
    (correct : ColorsCorrect (fun record => record.2.colors) color (plug (PhysicalPackedRotation.before right u v w p top) outside))
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι) (physicalUnique : Unique forest)
    (logicalUnique : ((plug (PhysicalPackedRotation.before right u v w p top) outside).inventory (fun record => identifier record.1)).Nodup)
    (represented : ProjectionForest.Represents color ⟨PhysicalPackedRotation.before right u v w p top,outside⟩ (erase forest)) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program identifier (identifier (firstRecord right p top).1) right) initial (encode forest)
        (.done (if right then identifier p.1 else identifier top.1)) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨PhysicalPackedRotation.after right u v w p top,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 780*Fintype.card C := by
  let first := firstRecord right p top
  let second := secondRecord right p top
  let l := leftSide right u v w p top
  let r := rightSide right u v w p top
  let root : Cursor α (LogicalRecord ρ η C) := ⟨.fork first l r,outside⟩
  let pivot := PackedDescentController.child (!right) l r first outside
  let wanted := identifier first.1
  have rootRep : ProjectionForest.Represents color root (erase forest) := by
    simpa only [before_shape] using represented
  have rootUnique : Distinguishes (fun record => identifier record.1) root.tree := by
    apply Multiset.inj_on_of_nodup_map
    simpa only [before_shape,Source.inventory,root,first,l,r,Cursor.tree] using logicalUnique
  have sameTree : pivot.tree = root.tree := by cases right <;> rfl
  have pivotRecord : pivot.focus.rootRecord = second := child_record right u v w p top outside
  obtain ⟨firstReads,firstCost,firstRun,firstBound⟩ :=
    PhysicalRecordFinder.find_current (fun record => identifier record.1) color root forest rootRep physicalUnique rootUnique
  have firstRun := PhysicalRecordFinder.write_labels _ _ firstRun
  have firstSteps := firstRun.map_prefix finishRead (read_code identifier wanted right)
  obtain ⟨downForest,downReads,downCost,downRun,downRep,downUnique,downBound⟩ :=
    PhysicalPackedChildController.descend_labels identifier color (!right) l r first outside rootReady forest rootRep physicalUnique rootUnique
  rw [child_id identifier right u v w p top] at downRun
  have downSteps := downRun.map_prefix (finishDescent first) (descent_code identifier wanted right first)
  obtain ⟨pivotReads,pivotCost,pivotRun,pivotBound⟩ :=
    PhysicalRecordFinder.find_current (fun record => identifier record.1) color pivot downForest downRep downUnique
      (by rw [sameTree]; exact rootUnique)
  have pivotRun := PhysicalRecordFinder.write_labels _ _ pivotRun
  rw [pivotRecord] at pivotRun
  have pivotSteps := pivotRun.map_prefix (finishPivot first (identifier second.1))
    (pivot_code identifier wanted (identifier second.1) right first)
  have parentField : pivot.focus.rootRecord.2.parent = some (identifier first.1) := by rw [pivotRecord]; exact parentReady
  obtain ⟨upForest,upReads,upCost,upRun,upRep,upUnique,upBound⟩ :=
    PhysicalPackedParentController.ascend_labels identifier color (!right) l r first outside parentField rootReady
      downForest downRep downUnique rootUnique
  rw [pivotRecord] at upRun
  have upSteps := upRun.map_prefix (finishAscent right first second) (ascent_code identifier wanted right first second)
  have restoredRep : ProjectionForest.Represents color ⟨PhysicalPackedRotation.before right u v w p top,outside⟩ (erase upForest) := by
    simpa only [before_shape] using upRep
  obtain ⟨target,rotationReads,rotationCost,rotationRun,targetRep,targetUnique,rotationBound⟩ :=
    PhysicalPackedRotation.rotate_labels (fun record => record.2.colors) color right u v w p top outside correct upForest upUnique restoredRep
  let data : Inputs ρ η C := ⟨u.support color,v.support color,w.support color,p,top⟩
  have rotationSteps := rotationRun.map_prefix (finishRotation identifier right data) (rotation_code identifier wanted right data)
  have nonempty : ((data.u ∪ data.v) ∪ data.w).Nonempty :=
    (u.support_nonempty color).mono (Finset.subset_union_left.trans Finset.subset_union_left)
  have startEq : finishRotation (ι := ι) identifier right data
      (.scan (((data.u ∪ data.v) ∪ data.w).sort (· ≤ ·))) =
      State.rotating data (.scan (((data.u ∪ data.v) ∪ data.w).sort (· ≤ ·))) := by
    cases sorted : ((data.u ∪ data.v) ∪ data.w).sort (· ≤ ·) with
    | nil =>
      have length := congrArg List.length sorted
      simp only [Finset.length_sort,List.length_nil] at length
      have positive := Finset.card_pos.mpr nonempty
      omega
    | cons => rfl
  rw [startEq] at rotationSteps
  have acquired : inputs right first second = some data := inputs_correct identifier color right u v w p top rootReady pivotReady
  have endpoint : finishAscent (ι := ι) right first second (.done (identifier first.1)) =
      State.rotating data (.scan (((data.u ∪ data.v) ∪ data.w).sort (· ≤ ·))) := by
    simp only [finishAscent,acquired]
  rw [endpoint] at upSteps
  have actual := ((((firstSteps.append downSteps).append pivotSteps).append upSteps).append rotationSteps).run rfl
  exact ⟨target,_,_,actual,targetRep,targetUnique,by omega⟩

end ChaCha.Paper20261030.PackedRotationProgram
