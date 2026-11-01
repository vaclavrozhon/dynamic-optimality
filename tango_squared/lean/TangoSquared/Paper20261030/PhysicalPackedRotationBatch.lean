import TangoSquared.Paper20261030.PhysicalPackedRotationKernel
import Mathlib.Data.Finset.Sort

/-! Serializing the observed rotation kernel over the relevant colors.
Unprocessed projections still represent the old source; processed ones
represent the new source. Each color is updated once. Colors absent from
the rotated subtree retain their active or parked physical positions.
-/

namespace TangoSquared.Paper20261030.PhysicalPackedRotation

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C]

inductive State (ρ ι C : Type*) where
  | scan (colors : List C)
  | rotating (q : C) (rest : List C) (phase : KernelState ρ ι C)

def finish (q : C) (rest : List C) : KernelState ρ ι C → State ρ ι C
  | .ready (.running .done) => .scan rest
  | phase => .rotating q rest phase

def program (mask : ρ → Finset C) (right : Bool) (u v w : Finset C) (p top : ρ) :
    Program (State ρ ι C) C (Record ρ ι)
  | .scan [] => .halt
  | .scan (q::rest) => (kernel mask right q u v w p top initial).mapState (finish q rest)
  | .rotating q rest phase => (kernel mask right q u v w p top phase).mapState (finish q rest)

theorem kernel_code (mask : ρ → Finset C) (right : Bool) (u v w : Finset C) (p top : ρ)
    (q : C) (rest : List C) (phase : KernelState ρ ι C) (active : kernel mask right q u v w p top phase ≠ .halt) :
    program mask right u v w p top (finish q rest phase) =
      (kernel mask right q u v w p top phase).mapState (finish q rest) := by
  cases phase with
  | running | error => rfl
  | ready state => cases state with
    | error => rfl
    | running phase => cases phase with
      | detaching | running => rfl
      | done => exact False.elim (active (by cases right <;> rfl))

theorem inactive [DecidableEq α] (color : α → C) (right : Bool) (q : C)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (missing : q ∉ (before right u v w p top).support color)
    (physical : Option (Cursor α (List ρ)))
    (represented : ProjectionForest.RepresentsAt color q ⟨before right u v w p top,outside⟩ physical) :
    ProjectionForest.RepresentsAt color q ⟨after right u v w p top,outside⟩ physical := by
  have same := same_support color right u v w p top
  cases physical with
  | none =>
    have operation : SourcePointer.Step ⟨before right u v w p top,outside⟩ ⟨after right u v w p top,outside⟩ := by
      cases right
      · exact .rotateLeft _ _ _ _ _ _
      · exact .rotateRight _ _ _ _ _ _
    have whole : (Cursor.tree ⟨before right u v w p top,outside⟩).support color =
        (Cursor.tree ⟨after right u v w p top,outside⟩).support color := by
      rw [Source.support_leaves,Source.support_leaves,operation.leaves]
    change q ∉ (Cursor.tree ⟨after right u v w p top,outside⟩).support color
    rw [← whole]
    exact represented
  | some physical =>
    have oldEmpty := (packed_none_iff color q (before right u v w p top)).mpr missing
    have newEmpty := (packed_none_iff color q (after right u v w p top)).mpr (same ▸ missing)
    have oldShape := packed_none_shape color q _ oldEmpty
    have newShape := packed_none_shape color q _ newEmpty
    refine ⟨(packed_eq_context color q same.symm (newEmpty.trans oldEmpty.symm) outside).trans represented.1,?_⟩
    simpa only [cursorShape,LeafPointer.project,oldShape,newShape,ite_true] using represented.2

theorem scan [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (right : Bool)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (before right u v w p top) outside))
    (colors : List C) (distinct : colors.Nodup)
    (permitted : ∀ q ∈ colors, q ∈ (before right u v w p top).support color)
    (forest : TaggedForest C α ρ ι) (unique : Unique forest)
    (pending : ∀ q ∈ colors, ProjectionForest.RepresentsAt color q ⟨before right u v w p top,outside⟩ (erase forest q))
    (finished : ∀ q, q ∉ colors → ProjectionForest.RepresentsAt color q ⟨after right u v w p top,outside⟩ (erase forest q)) :
    ∃ target reads cost,
      Run (program mask right (u.support color) (v.support color) (w.support color) p top)
        (.scan colors) (encode forest) (.scan []) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨after right u v w p top,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 646*colors.length := by
  induction colors generalizing forest with
  | nil => exact ⟨forest,[],0,.halt rfl,fun q => finished q (by simp),unique,by omega⟩
  | cons q rest ih =>
    have nodup := List.nodup_cons.mp distinct
    obtain ⟨middle,firstReads,firstCost,firstRun,newRep,unchanged,middleUnique,firstBound⟩ :=
      run mask color right q u v w p top outside correct (permitted q (List.mem_cons_self)) forest unique
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

theorem rotate [DecidableEq α] [Fintype C] (mask : ρ → Finset C) (color : α → C) (right : Bool)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (before right u v w p top) outside))
    (forest : TaggedForest C α ρ ι) (unique : Unique forest)
    (represented : ProjectionForest.Represents color ⟨before right u v w p top,outside⟩ (erase forest)) :
    ∃ target reads cost,
      Run (program mask right (u.support color) (v.support color) (w.support color) p top)
        (.scan (((u.support color ∪ v.support color) ∪ w.support color).sort (· ≤ ·)))
        (encode forest) (.scan []) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨after right u v w p top,outside⟩ (erase target) ∧
      Unique target ∧ cost ≤ 646*Fintype.card C := by
  let selected := (u.support color ∪ v.support color) ∪ w.support color
  have support : (before right u v w p top).support color = selected := by
    cases right <;> simp [before,Source.support,selected,Finset.union_assoc]
  obtain ⟨target,reads,cost,actual,targetRep,targetUnique,bounded⟩ :=
    scan mask color right u v w p top outside correct (selected.sort (· ≤ ·)) (selected.sort_nodup (· ≤ ·))
      (fun q member => support ▸ ((Finset.mem_sort (· ≤ ·)).mp member)) forest unique
      (fun q _ => represented q) (fun q absent => inactive color right q u v w p top outside
        (by rw [support]; exact fun member => absent ((Finset.mem_sort (· ≤ ·)).mpr member)) (erase forest q) (represented q))
  refine ⟨target,reads,cost,actual,targetRep,targetUnique,?_⟩
  have capacity := Finset.card_le_univ selected
  simp only [Finset.length_sort] at bounded
  omega

end TangoSquared.Paper20261030.PhysicalPackedRotation
