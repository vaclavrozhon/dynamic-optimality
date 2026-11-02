import ChaCha.Paper20261030.LocalProjectedRotation
import ChaCha.Paper20261030.LocalPackedContextProgram

/-! Instantiating the local projected rotation from observed masks.
Ownership, presence of the three pieces, and the ancestor-prefix test are
computed from record values. This is the per-color kernel; obtaining the
two pivot records and serializing all colors are separate controllers.
-/

namespace ChaCha.Paper20261030.PackedRotationController

open ColoredStorage SourcePointer SourceLocalProgram ProjectionLocal
open LocalRecordActions (Action)

variable {α ρ C : Type*} [LinearOrder C]

def ownerMask (left right : Finset C) : Option C :=
  if h : (left ∩ right).Nonempty then some ((left ∩ right).min' h)
  else if h : (left ∪ right).Nonempty then some ((left ∪ right).min' h) else none

theorem ownerMask_source (color : α → C) (left right : Source α ρ) :
    ownerMask (left.support color) (right.support color) = some (owner color left right) := by
  unfold ownerMask owner
  split
  · rfl
  · rw [dif_pos (Finset.Nonempty.mono Finset.subset_union_left (left.support_nonempty color))]

theorem packed_isSome [DecidableEq α] (color : α → C) (q : C) (source : Source α ρ) :
    (packed color q source).isSome = decide (q ∈ source.support color) := by
  by_cases present : q ∈ source.support color
  · obtain ⟨actual,found⟩ := packed_exists color q source present
    simp only [found,Option.isSome_some,present,decide_true]
  · simp only [(packed_none_iff color q source).mpr present,Option.isSome_none,present,decide_false]

def actions (q : C) (u v w : Finset C) (p top : ρ) : List (Action ρ) :=
  LocalProjectedRotation.actions (decide (q ∈ u)) (decide (q ∈ v)) (decide (q ∈ w)) p top
    (decide (ownerMask u v = some q)) (decide (ownerMask (u ∪ v) w = some q))
    (decide (ownerMask u (v ∪ w) = some q)) (decide (ownerMask v w = some q))

def program (mask : ρ → Finset C) (q : C) (u v w : Finset C) (p top : ρ) :
    Program (PackedContextController.State ρ) (List ρ) :=
  PackedContextController.program mask ((u ∪ v) ∪ w) (actions q u v w p top)

theorem projected [DecidableEq α] (color : α → C) (q : C)
    (u v w : Source α ρ) (p top : ρ) :
    LocalProjectedRotation.Transforms (actions q (u.support color) (v.support color) (w.support color) p top)
      (packed color q (.fork top (.fork p u v) w)) (packed color q (.fork p u (.fork top v w))) 13 := by
  have oldTop := ownerMask_source color (.fork p u v) w
  have newTop := ownerMask_source color u (.fork top v w)
  simp only [Source.support] at oldTop newTop
  simp only [actions,ownerMask_source,oldTop,newTop,Option.some.injEq,packed_fork]
  simpa only [packed_isSome] using LocalProjectedRotation.rotation
    (packed color q u) (packed color q v) (packed color q w) p top
    (decide (owner color u v = q)) (decide (owner color (.fork p u v) w = q))
    (decide (owner color u (.fork top v w) = q)) (decide (owner color v w = q))

theorem rotate_right [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (q : C)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (.fork top (.fork p u v) w) outside))
    (present : q ∈ (Source.fork top (.fork p u v) w).support color)
    (physical : Cursor α (List ρ))
    (represented : ColoredStorage.Represents color q ⟨.fork top (.fork p u v) w,outside⟩ physical) :
    ∃ target reads cost,
      Run (program mask q (u.support color) (v.support color) (w.support color) p top)
        (.detaching .start) physical .done target reads cost ∧
      ColoredStorage.Represents color q ⟨.fork p u (.fork top v w),outside⟩ target ∧ cost ≤ 17 := by
  have sameColors : (Source.fork top (.fork p u v) w).support color =
      (Source.fork p u (.fork top v w)).support color := by simp only [Source.support,Finset.union_assoc]
  obtain ⟨a,packedBefore⟩ := packed_exists color q (.fork top (.fork p u v) w) present
  obtain ⟨b,packedAfter⟩ := packed_exists color q (.fork p u (.fork top v w)) (sameColors ▸ present)
  have kernel := projected color q u v w p top
  rw [packedBefore,packedAfter] at kernel
  exact PackedContextController.lift mask color q _ _ outside sameColors correct a b packedBefore packedAfter
    (actions q (u.support color) (v.support color) (w.support color) p top) 13 kernel physical represented

def leftActions (q : C) (u v w : Finset C) (p top : ρ) : List (Action ρ) :=
  LocalProjectedRotation.actionsLeft (decide (q ∈ u)) (decide (q ∈ v)) (decide (q ∈ w)) p top
    (decide (ownerMask u v = some q)) (decide (ownerMask (u ∪ v) w = some q))
    (decide (ownerMask u (v ∪ w) = some q)) (decide (ownerMask v w = some q))

def leftProgram (mask : ρ → Finset C) (q : C) (u v w : Finset C) (p top : ρ) :
    Program (PackedContextController.State ρ) (List ρ) :=
  PackedContextController.program mask (u ∪ (v ∪ w)) (leftActions q u v w p top)

theorem projected_left [DecidableEq α] (color : α → C) (q : C)
    (u v w : Source α ρ) (p top : ρ) :
    LocalProjectedRotation.Transforms (leftActions q (u.support color) (v.support color) (w.support color) p top)
      (packed color q (.fork p u (.fork top v w))) (packed color q (.fork top (.fork p u v) w)) 13 := by
  have oldTop := ownerMask_source color (.fork p u v) w
  have newTop := ownerMask_source color u (.fork top v w)
  simp only [Source.support] at oldTop newTop
  simp only [leftActions,ownerMask_source,oldTop,newTop,Option.some.injEq,packed_fork]
  simpa only [packed_isSome] using LocalProjectedRotation.rotation_left
    (packed color q u) (packed color q v) (packed color q w) p top
    (decide (owner color u v = q)) (decide (owner color (.fork p u v) w = q))
    (decide (owner color u (.fork top v w) = q)) (decide (owner color v w = q))

theorem rotate_left [DecidableEq α] (mask : ρ → Finset C) (color : α → C) (q : C)
    (u v w : Source α ρ) (p top : ρ) (outside : List (Frame α ρ))
    (correct : ColorsCorrect mask color (plug (.fork p u (.fork top v w)) outside))
    (present : q ∈ (Source.fork p u (.fork top v w)).support color)
    (physical : Cursor α (List ρ))
    (represented : ColoredStorage.Represents color q ⟨.fork p u (.fork top v w),outside⟩ physical) :
    ∃ target reads cost,
      Run (leftProgram mask q (u.support color) (v.support color) (w.support color) p top)
        (.detaching .start) physical .done target reads cost ∧
      ColoredStorage.Represents color q ⟨.fork top (.fork p u v) w,outside⟩ target ∧ cost ≤ 17 := by
  have sameColors : (Source.fork p u (.fork top v w)).support color =
      (Source.fork top (.fork p u v) w).support color := by simp only [Source.support,Finset.union_assoc]
  obtain ⟨a,packedBefore⟩ := packed_exists color q (.fork p u (.fork top v w)) present
  obtain ⟨b,packedAfter⟩ := packed_exists color q (.fork top (.fork p u v) w) (sameColors ▸ present)
  have kernel := projected_left color q u v w p top
  rw [packedBefore,packedAfter] at kernel
  exact PackedContextController.lift mask color q _ _ outside sameColors correct a b packedBefore packedAfter
    (leftActions q (u.support color) (v.support color) (w.support color) p top) 13 kernel physical represented

end ChaCha.Paper20261030.PackedRotationController
