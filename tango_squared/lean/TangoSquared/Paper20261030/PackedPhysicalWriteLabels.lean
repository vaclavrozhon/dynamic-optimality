import TangoSquared.Paper20261030.PhysicalForestWriteLabels
import TangoSquared.Paper20261030.PhysicalPackedWrite
import TangoSquared.Paper20261030.PhysicalPackedChildProgram
import TangoSquared.Paper20261030.PhysicalPackedRotationBatch

set_option autoImplicit false

/-! The existing packed write, child navigation, and rotation controllers
with per-write physical-id preservation. Their programs, representations,
and operation bounds are unchanged. -/
namespace TangoSquared.Paper20261030.PhysicalPackedWriteController

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem write_labels [DecidableEq α] (identifier : ρ → η) (color : α → C) (source : Cursor α ρ)
    (fresh : ρ) (sameId : identifier fresh = identifier source.focus.rootRecord)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (physicalUnique : Unique forest) (logicalUnique : (source.tree.inventory identifier).Nodup) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program identifier (identifier source.focus.rootRecord) fresh)
        (.ready (.scan (Finset.univ.sort (· ≤ ·)))) (encode forest) (.ready .done) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨source.focus.setRoot fresh,source.ancestors⟩ (erase target) ∧
      Unique target ∧ ((Cursor.tree ⟨source.focus.setRoot fresh,source.ancestors⟩).inventory identifier).Nodup ∧
      cost ≤ 38*(Fintype.card C+1) := by
  obtain ⟨bare,readWord,sourceCost,sourceRun,bareRep,bounded⟩ :=
    PackedWriteController.write identifier color source fresh (erase forest) represented logicalUnique
  obtain ⟨target,reads,cost,actual,targetErases,targetUnique,actualBound⟩ :=
    PhysicalForestCompiler.compile_write_labels _ sourceRun forest rfl physicalUnique
  have inventory := plug_inventory_congr identifier (Source.inventory_setRoot identifier source.focus fresh sameId) source.ancestors
  refine ⟨target,reads,cost,actual,?_,targetUnique,?_,by omega⟩
  · rw [targetErases]; exact bareRep
  · change ((plug (source.focus.setRoot fresh) source.ancestors).inventory identifier).Nodup
    rw [inventory]
    exact logicalUnique

end TangoSquared.Paper20261030.PhysicalPackedWriteController

namespace TangoSquared.Paper20261030.PhysicalPackedChildController

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

theorem descend_labels [DecidableEq α] (identifier : ρ → η) (color : α → C) (right : Bool)
    (l r : Source α (ρ × Fields η C)) (record : ρ × Fields η C) (outside)
    (children : record.2.children = some
      (Child.mk (identifier l.rootRecord.1) (l.support color),Child.mk (identifier r.rootRecord.1) (r.support color)))
    (forest : TaggedForest C α (ρ × Fields η C) ι)
    (represented : ProjectionForest.Represents color ⟨.fork record l r,outside⟩ (erase forest))
    (physicalUnique : Unique forest)
    (logicalUnique : Distinguishes (fun entry => identifier entry.1) (Cursor.tree ⟨.fork record l r,outside⟩)) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program identifier (identifier record.1) right) initial (encode forest)
        (.ready (.done (if right then identifier r.rootRecord.1 else identifier l.rootRecord.1))) (encode target) reads cost ∧
      ProjectionForest.Represents color (PackedDescentController.child right l r record outside) (erase target) ∧
      Unique target ∧ cost ≤ 76*Fintype.card C := by
  obtain ⟨bare,readWord,sourceCost,sourceRun,bareRep,bounded⟩ :=
    PackedChildController.descend identifier color right l r record outside children (erase forest) represented logicalUnique
  obtain ⟨target,reads,cost,actual,targetErases,targetUnique,actualBound⟩ :=
    PhysicalForestCompiler.compile_write_labels _ sourceRun forest rfl physicalUnique
  exact ⟨target,reads,cost,actual,by rw [targetErases]; exact bareRep,targetUnique,by omega⟩

end TangoSquared.Paper20261030.PhysicalPackedChildController

namespace TangoSquared.Paper20261030.PhysicalPackedRotation

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

theorem run_labels [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (right : Bool) (q : C)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (before right u v w p top) outside))
    (present : q ∈ (before right u v w p top).support color)
    (forest : TaggedForest C α ρ ι) (unique : Unique forest)
    (represented : ProjectionForest.RepresentsAt color q ⟨before right u v w p top,outside⟩ (erase forest q)) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (kernel mask right q (u.support color) (v.support color) (w.support color) p top)
        initial (encode forest) finalState (encode target) reads cost ∧
      ProjectionForest.RepresentsAt color q ⟨after right u v w p top,outside⟩ (erase target q) ∧
      (∀ other, other ≠ q → erase target other = erase forest other) ∧ Unique target ∧ cost ≤ 646 := by
  cases location : erase forest q with
  | none =>
    rw [location] at represented
    exact False.elim (represented (ProjectionForest.support_focus color _ outside present))
  | some physical =>
    rw [location] at represented
    have localRun : ∃ actual reads cost,
        SourceLocalProgram.Run
          (if right then PackedRotationController.program mask q (u.support color) (v.support color) (w.support color) p top
            else PackedRotationController.leftProgram mask q (u.support color) (v.support color) (w.support color) p top)
          (.detaching .start) physical .done actual reads cost ∧
        ColoredStorage.Represents color q ⟨after right u v w p top,outside⟩ actual ∧ cost ≤ 17 := by
      cases right with
      | false => exact PackedRotationController.rotate_left mask color q u v w p top outside correct present physical represented
      | true => exact PackedRotationController.rotate_right mask color q u v w p top outside correct present physical represented
    obtain ⟨actual,localReads,localCost,body,actualRep,localBound⟩ := localRun
    have inForest := ForestCursorLift.run q body (erase forest) location
    obtain ⟨target,reads,cost,compiled,targetErases,targetUnique,bounded⟩ :=
      PhysicalForestCompiler.compile_write_labels _ inForest forest rfl unique
    refine ⟨target,reads,cost,compiled,?_,?_,targetUnique,by omega⟩
    · rw [targetErases,Function.update_self]
      exact actualRep
    · intro other different
      rw [targetErases,Function.update_of_ne different]

end TangoSquared.Paper20261030.PhysicalPackedRotation

namespace TangoSquared.Paper20261030.PhysicalPackedRotation

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

theorem scan_labels [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (right : Bool)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (before right u v w p top) outside))
    (colors : List C) (distinct : colors.Nodup)
    (permitted : ∀ q ∈ colors, q ∈ (before right u v w p top).support color)
    (forest : TaggedForest C α ρ ι) (unique : Unique forest)
    (pending : ∀ q ∈ colors, ProjectionForest.RepresentsAt color q ⟨before right u v w p top,outside⟩ (erase forest q))
    (finished : ∀ q, q ∉ colors → ProjectionForest.RepresentsAt color q ⟨after right u v w p top,outside⟩ (erase forest q)) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program mask right (u.support color) (v.support color) (w.support color) p top)
        (.scan colors) (encode forest) (.scan []) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨after right u v w p top,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 646*colors.length := by
  induction colors generalizing forest with
  | nil => exact ⟨forest,[],0,.halt rfl,fun q => finished q (by simp),unique,by omega⟩
  | cons q rest ih =>
    have nodup := List.nodup_cons.mp distinct
    obtain ⟨middle,firstReads,firstCost,firstRun,newRep,unchanged,middleUnique,firstBound⟩ :=
      run_labels mask color right q u v w p top outside correct (permitted q (List.mem_cons_self)) forest unique
        (pending q (List.mem_cons_self))
    have nextPending : ∀ other ∈ rest,
        ProjectionForest.RepresentsAt color other ⟨before right u v w p top,outside⟩ (erase middle other) := by
      intro other member
      have different : other ≠ q := fun equal => nodup.1 (equal ▸ member)
      rw [unchanged other different]
      exact pending other (List.mem_cons_of_mem _ member)
    have nextFinished : ∀ other, other ∉ rest →
        ProjectionForest.RepresentsAt color other ⟨after right u v w p top,outside⟩ (erase middle other) := by
      intro other absent
      by_cases equal : other = q
      · subst other; exact newRep
      · rw [unchanged other equal]
        exact finished other (by simpa only [List.mem_cons,not_or] using And.intro equal absent)
    obtain ⟨target,lastReads,lastCost,lastRun,targetRep,targetUnique,lastBound⟩ :=
      ih nodup.2 (fun other member => permitted other (List.mem_cons_of_mem _ member)) middle middleUnique nextPending nextFinished
    have positive : 0 < firstCost := by cases firstRun with
      | next => omega
    have front := firstRun.map_prefix (finish q rest)
      (kernel_code mask right (u.support color) (v.support color) (w.support color) p top q rest)
    have start := front.change_start (replacement := .scan (q::rest)) positive (by rfl)
    exact ⟨target,firstReads++lastReads,firstCost+lastCost,start.then_run lastRun,targetRep,targetUnique,
      by simp only [List.length_cons]; omega⟩

theorem rotate_labels [DecidableEq α] [Fintype C] (mask : ρ → Finset C) (color : α → C) (right : Bool)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (before right u v w p top) outside))
    (forest : TaggedForest C α ρ ι) (unique : Unique forest)
    (represented : ProjectionForest.Represents color ⟨before right u v w p top,outside⟩ (erase forest)) :
    ∃ target reads cost,
      ForestWriteLabels.Run (fun record => record.1.1) (program mask right (u.support color) (v.support color) (w.support color) p top)
        (.scan (((u.support color ∪ v.support color) ∪ w.support color).sort (· ≤ ·)))
        (encode forest) (.scan []) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨after right u v w p top,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 646*Fintype.card C := by
  let selected := (u.support color ∪ v.support color) ∪ w.support color
  have support : (before right u v w p top).support color = selected := by
    cases right <;> simp [before,Source.support,selected,Finset.union_assoc]
  obtain ⟨target,reads,cost,actual,targetRep,targetUnique,bounded⟩ :=
    scan_labels mask color right u v w p top outside correct (selected.sort (· ≤ ·)) (selected.sort_nodup (· ≤ ·))
      (fun q member => support ▸ ((Finset.mem_sort (· ≤ ·)).mp member)) forest unique
      (fun q _ => represented q) (fun q absent => inactive color right q u v w p top outside
        (by rw [support]; exact fun member => absent ((Finset.mem_sort (· ≤ ·)).mpr member)) (erase forest q) (represented q))
  refine ⟨target,reads,cost,actual,targetRep,targetUnique,?_⟩
  have capacity := Finset.card_le_univ selected
  simp only [Finset.length_sort] at bounded
  omega

end TangoSquared.Paper20261030.PhysicalPackedRotation
