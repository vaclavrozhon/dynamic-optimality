import TangoSquared.Paper20261030.HeadMemorySplice

/-!
# Primary component roots indexed by their original endpoint keys

`componentStart t key` is the depth of the preferred path ending at `key`.
The root preferred endpoint has depth zero. Every other endpoint belongs
to a child component, with its child-relative start increased by one.
A head switch changes precisely the old and incoming endpoints' starts.
-/

namespace TangoSquared.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

def componentStart : PrefRouter α → α → Nat
  | .leaf _,_ => 0
  | t@(.fork _ left right),key =>
      if key = t.terminal then 0
      else if key ∈ left.leaves then componentStart left key + 1 else componentStart right key + 1

theorem componentStart_terminal (primary : PrefRouter α) : primary.componentStart primary.terminal = 0 := by
  cases primary <;> simp [componentStart]

theorem HeadStep.endpoints_ne {x : α} {d : Nat} {before after : PrefRouter α}
    (step : HeadStep x d before after) (distinct : before.leaves.Nodup) : before.terminal ≠ after.terminal := by
  induction step with
  | leftRoot left right member =>
    obtain ⟨_,_,disjoint⟩ := List.nodup_append.mp distinct
    exact fun same => disjoint _ left.terminal_mem _ right.terminal_mem same.symm
  | rightRoot left right notLeft member =>
    obtain ⟨_,_,disjoint⟩ := List.nodup_append.mp distinct
    exact fun same => disjoint _ left.terminal_mem _ right.terminal_mem same
  | leftDown right step ih => exact ih (List.nodup_append.mp distinct).1
  | rightDown left notLeft step ih => exact ih (List.nodup_append.mp distinct).2.1

theorem HeadStep.componentStart_unchanged {x : α} {d : Nat} {before after : PrefRouter α}
    (step : HeadStep x d before after) (key : α)
    (oldOther : key ≠ before.terminal) (newOther : key ≠ after.terminal) :
    after.componentStart key = before.componentStart key := by
  induction step with
  | leftRoot left right member => simp only [componentStart,if_neg oldOther,if_neg newOther]
  | rightRoot left right notLeft member => simp only [componentStart,if_neg oldOther,if_neg newOther]
  | leftDown right step ih =>
    simp only [componentStart,if_neg oldOther,if_neg newOther,step.leaves,ih oldOther newOther]
  | rightDown left notLeft step ih =>
    simp only [componentStart,if_neg oldOther,if_neg newOther,ih oldOther newOther]

theorem HeadStep.old_componentStart {x : α} {d : Nat} {before after : PrefRouter α}
    (step : HeadStep x d before after) (distinct : before.leaves.Nodup) :
    after.componentStart before.terminal = d+1 := by
  induction step with
  | leftRoot left right member =>
    obtain ⟨_,_,disjoint⟩ := List.nodup_append.mp distinct
    have different : right.terminal ≠ left.terminal :=
      fun same => disjoint _ left.terminal_mem _ right.terminal_mem same.symm
    have outside : right.terminal ∉ left.leaves :=
      fun member => disjoint _ member _ right.terminal_mem rfl
    simp [componentStart,terminal,different,outside,componentStart_terminal]
  | rightRoot left right notLeft member =>
    obtain ⟨_,_,disjoint⟩ := List.nodup_append.mp distinct
    have different : left.terminal ≠ right.terminal :=
      fun same => disjoint _ left.terminal_mem _ right.terminal_mem same
    simp [componentStart,terminal,different,left.terminal_mem,componentStart_terminal]
  | @leftDown d left newLeft right step ih =>
    have dl := (List.nodup_append.mp distinct).1
    have different := step.endpoints_ne dl
    have inside : left.terminal ∈ newLeft.leaves := by rw [step.leaves]; exact left.terminal_mem
    simpa [componentStart,terminal,different,inside,Nat.add_assoc] using ih dl
  | @rightDown d right newRight left notLeft step ih =>
    obtain ⟨_,dr,disjoint⟩ := List.nodup_append.mp distinct
    have different := step.endpoints_ne dr
    have outside : right.terminal ∉ left.leaves := fun member => disjoint _ member _ right.terminal_mem rfl
    simpa [componentStart,terminal,different,outside,Nat.add_assoc] using ih dr

theorem HeadStep.incoming_componentStart {x : α} {d : Nat} {before after : PrefRouter α}
    (step : HeadStep x d before after) (distinct : before.leaves.Nodup) :
    before.componentStart after.terminal = d+1 := by
  induction step with
  | leftRoot left right member =>
    obtain ⟨_,_,disjoint⟩ := List.nodup_append.mp distinct
    have different : left.terminal ≠ right.terminal :=
      fun same => disjoint _ left.terminal_mem _ right.terminal_mem same
    simp [componentStart,terminal,different,left.terminal_mem,componentStart_terminal]
  | rightRoot left right notLeft member =>
    obtain ⟨_,_,disjoint⟩ := List.nodup_append.mp distinct
    have different : right.terminal ≠ left.terminal :=
      fun same => disjoint _ left.terminal_mem _ right.terminal_mem same.symm
    have outside : right.terminal ∉ left.leaves := fun member => disjoint _ member _ right.terminal_mem rfl
    simp [componentStart,terminal,different,outside,componentStart_terminal]
  | @leftDown d left newLeft right step ih =>
    have dl := (List.nodup_append.mp distinct).1
    have different := (step.endpoints_ne dl).symm
    have inside : newLeft.terminal ∈ left.leaves := by rw [← step.leaves]; exact newLeft.terminal_mem
    simpa [componentStart,terminal,different,inside,Nat.add_assoc] using ih dl
  | @rightDown d right newRight left notLeft step ih =>
    obtain ⟨_,dr,disjoint⟩ := List.nodup_append.mp distinct
    have different := (step.endpoints_ne dr).symm
    have inRight : newRight.terminal ∈ right.leaves := by rw [← step.leaves]; exact newRight.terminal_mem
    have outside : newRight.terminal ∉ left.leaves := fun member => disjoint _ member _ inRight rfl
    simpa [componentStart,terminal,different,outside,Nat.add_assoc] using ih dr

end TangoSquared.PreferredProjection.PrefRouter
