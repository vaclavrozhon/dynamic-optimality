import TangoSquared.Paper20261030.LocalPackedRotationProgram
import TangoSquared.Paper20261030.PackedIdentifierUniqueness

/-! Correctness of the complete read-driven rotation controller. The
premises concern the child and parent fields actually inspected and the
color masks needed to classify unchanged ancestor records. The result is
the exact raw source rotation; prescribed subsequent source writes update
the logical pivot fields. Physical pointer fields are maintained throughout.
-/

namespace TangoSquared.Paper20261030.PackedRotationProgram

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

def firstRecord (right : Bool) (p top : LogicalRecord ρ η C) : LogicalRecord ρ η C := if right then top else p
def secondRecord (right : Bool) (p top : LogicalRecord ρ η C) : LogicalRecord ρ η C := if right then p else top

def leftSide (right : Bool) (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) : Source α (LogicalRecord ρ η C) :=
  if right then .fork p u v else u

def rightSide (right : Bool) (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) : Source α (LogicalRecord ρ η C) :=
  if right then w else .fork top v w

theorem before_shape (right : Bool) (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) :
    PhysicalPackedRotation.before right u v w p top =
      .fork (firstRecord right p top) (leftSide right u v w p top) (rightSide right u v w p top) := by
  cases right <;> rfl

theorem child_record (right : Bool) (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) (outside) :
    (PackedDescentController.child (!right) (leftSide right u v w p top) (rightSide right u v w p top)
      (firstRecord right p top) outside).focus.rootRecord = secondRecord right p top := by
  cases right <;> rfl

theorem child_id (identifier : ρ → η) (right : Bool) (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) :
    (if !right then identifier (rightSide right u v w p top).rootRecord.1
      else identifier (leftSide right u v w p top).rootRecord.1) = identifier (secondRecord right p top).1 := by
  cases right <;> rfl

def RootReady (identifier : ρ → η) (color : α → C) (right : Bool)
    (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) : Prop :=
  (firstRecord right p top).2.children = some
    (Child.mk (identifier (leftSide right u v w p top).rootRecord.1) ((leftSide right u v w p top).support color),
     Child.mk (identifier (rightSide right u v w p top).rootRecord.1) ((rightSide right u v w p top).support color))

def PivotReady (identifier : ρ → η) (color : α → C) (right : Bool)
    (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) : Prop :=
  (secondRecord right p top).2.children =
    if right then some (Child.mk (identifier u.rootRecord.1) (u.support color),Child.mk (identifier v.rootRecord.1) (v.support color))
    else some (Child.mk (identifier v.rootRecord.1) (v.support color),Child.mk (identifier w.rootRecord.1) (w.support color))

theorem inputs_correct (identifier : ρ → η) (color : α → C) (right : Bool)
    (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C)
    (rootReady : RootReady identifier color right u v w p top) (pivotReady : PivotReady identifier color right u v w p top) :
    inputs right (firstRecord right p top) (secondRecord right p top) =
      some ⟨u.support color,v.support color,w.support color,p,top⟩ := by
  cases right <;> simp only [RootReady,PivotReady,firstRecord,secondRecord,leftSide,rightSide,
    Bool.false_eq_true,if_false,ite_true] at rootReady pivotReady ⊢
  all_goals simp only [inputs,rootReady,pivotReady,Bool.false_eq_true,if_false,ite_true]

theorem rotate [DecidableEq α] (identifier : ρ → η) (color : α → C) (right : Bool)
    (u v w : Source α (LogicalRecord ρ η C)) (p top : LogicalRecord ρ η C) (outside : List (Frame α (LogicalRecord ρ η C)))
    (rootReady : RootReady identifier color right u v w p top)
    (pivotReady : PivotReady identifier color right u v w p top)
    (parentReady : (secondRecord right p top).2.parent = some (identifier (firstRecord right p top).1))
    (correct : ColorsCorrect (fun record => record.2.colors) color (plug (PhysicalPackedRotation.before right u v w p top) outside))
    (forest : TaggedForest C α (LogicalRecord ρ η C) ι) (physicalUnique : Unique forest)
    (logicalUnique : ((plug (PhysicalPackedRotation.before right u v w p top) outside).inventory (fun record => identifier record.1)).Nodup)
    (represented : ProjectionForest.Represents color ⟨PhysicalPackedRotation.before right u v w p top,outside⟩ (erase forest)) :
    ∃ target reads cost,
      Run (program identifier (identifier (firstRecord right p top).1) right) initial (encode forest)
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
  have firstSteps := firstRun.map_prefix finishRead (read_code identifier wanted right)
  obtain ⟨downForest,downReads,downCost,downRun,downRep,downUnique,downBound⟩ :=
    PhysicalPackedChildController.descend identifier color (!right) l r first outside rootReady forest rootRep physicalUnique rootUnique
  rw [child_id identifier right u v w p top] at downRun
  have downSteps := downRun.map_prefix (finishDescent first) (descent_code identifier wanted right first)
  obtain ⟨pivotReads,pivotCost,pivotRun,pivotBound⟩ :=
    PhysicalRecordFinder.find_current (fun record => identifier record.1) color pivot downForest downRep downUnique
      (by rw [sameTree]; exact rootUnique)
  rw [pivotRecord] at pivotRun
  have pivotSteps := pivotRun.map_prefix (finishPivot first (identifier second.1))
    (pivot_code identifier wanted (identifier second.1) right first)
  have parentField : pivot.focus.rootRecord.2.parent = some (identifier first.1) := by rw [pivotRecord]; exact parentReady
  obtain ⟨upForest,upReads,upCost,upRun,upRep,upUnique,upBound⟩ :=
    PhysicalPackedParentController.ascend identifier color (!right) l r first outside parentField rootReady
      downForest downRep downUnique rootUnique
  rw [pivotRecord] at upRun
  have upSteps := upRun.map_prefix (finishAscent right first second) (ascent_code identifier wanted right first second)
  have restoredRep : ProjectionForest.Represents color ⟨PhysicalPackedRotation.before right u v w p top,outside⟩ (erase upForest) := by
    simpa only [before_shape] using upRep
  obtain ⟨target,rotationReads,rotationCost,rotationRun,targetRep,targetUnique,rotationBound⟩ :=
    PhysicalPackedRotation.rotate (fun record => record.2.colors) color right u v w p top outside correct upForest upUnique restoredRep
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

end TangoSquared.Paper20261030.PackedRotationProgram
