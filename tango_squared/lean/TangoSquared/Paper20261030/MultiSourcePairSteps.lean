import TangoSquared.Paper20261030.MultiSourcePair

/-! One actual instruction within either piece is one actual instruction
in their joined tree. The other piece's fingers stay on their vertices,
including during rotations. The scope condition is only about which
finger registers the instruction uses, never about a supplied execution.
-/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions

variable {α ρ F σ : Type*} [DecidableEq F]

def Instruction.targets : Instruction σ F ρ → List F
  | .halt => []
  | .read finger _ | .nav finger _ _ | .write finger _ _ => [finger]
  | .copy destination origin _ => [destination,origin]

theorem copy_join_left (record : ρ) (left right : Configuration F α ρ) (destination origin : F)
    (destinationFree : right.fingers destination = none) (originFree : right.fingers origin = none) :
    copyResult (join record left right) destination origin = join record (copyResult left destination origin) right := by
  apply congrArg₂ Configuration.mk
  · rfl
  · funext other
    by_cases same : other = destination
    · subst other
      simp [copyResult,join,destinationFree,originFree]
    · simp only [copyResult,join,Function.update_of_ne same]

theorem copy_join_right (record : ρ) (left right : Configuration F α ρ) (destination origin : F)
    (destinationFree : left.fingers destination = none) (originFree : left.fingers origin = none) :
    copyResult (join record left right) destination origin = join record left (copyResult right destination origin) := by
  apply congrArg₂ Configuration.mk
  · rfl
  · funext other
    by_cases same : other = destination
    · subst other
      simp [copyResult,join,destinationFree,originFree]
    · simp only [copyResult,join,Function.update_of_ne same]

theorem Step.join_left {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (execution : Step source state before next after entry) (record : ρ) (other : Configuration F α ρ)
    (unused : ∀ finger ∈ (source state).targets, other.fingers finger = none) :
    Step source state (join record before other) next (join record after other) entry := by
  cases execution with
  | readNone instruction absent =>
    rename_i finger nextRead
    exact .readNone instruction (by simp only [join,absent,unused finger (by simp [instruction,Instruction.targets]),Option.map_none])
  | readSome instruction present reached =>
    rename_i finger position current nextRead
    exact .readSome (current := current.extend [.left record other.tree]) (position := false::position)
      instruction (by simp only [join,present]) (locate_left reached record other.tree)
  | nav instruction present reached moved =>
    have actual := Step.nav instruction (show (join record before other).fingers _ = some (false::_) by simp only [join,present])
      (locate_left reached record other.tree) (navigate_extend _ moved [.left record other.tree])
    simpa only [move_join_left] using actual
  | write instruction present reached =>
    have actual := Step.write instruction (show (join record before other).fingers _ = some (false::_) by simp only [join,present])
      (locate_left reached record other.tree)
    simpa only [write_join_left] using actual
  | copy instruction =>
    rename_i destination origin
    have destinationFree := unused destination (by simp [instruction,Instruction.targets])
    have originFree := unused origin (by simp [instruction,Instruction.targets])
    rw [← copy_join_left record before other destination origin destinationFree originFree]
    exact .copy instruction

theorem Step.join_right {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (execution : Step source state before next after entry) (record : ρ) (other : Configuration F α ρ)
    (unused : ∀ finger ∈ (source state).targets, other.fingers finger = none) :
    Step source state (join record other before) next (join record other after) entry := by
  cases execution with
  | readNone instruction absent =>
    rename_i finger nextRead
    exact .readNone instruction (by simp only [join,unused finger (by simp [instruction,Instruction.targets]),absent,Option.map_none])
  | readSome instruction present reached =>
    rename_i finger position current nextRead
    have free := unused finger (by simp [instruction,Instruction.targets])
    exact .readSome (current := current.extend [.right other.tree record]) (position := true::position)
      instruction (by simp only [join,free,present,Option.map_some]) (locate_right reached record other.tree)
  | nav instruction present reached moved =>
    rename_i finger position current target action
    have free := unused finger (by simp [instruction,Instruction.targets])
    have actual := Step.nav instruction
      (show (join record other before).fingers finger = some (true::position) by simp only [join,free,present,Option.map_some])
      (locate_right reached record other.tree) (navigate_extend _ moved [.right other.tree record])
    simpa only [move_join_right record other before finger free] using actual
  | write instruction present reached =>
    rename_i finger position current fresh
    have free := unused finger (by simp [instruction,Instruction.targets])
    have actual := Step.write instruction
      (show (join record other before).fingers finger = some (true::position) by simp only [join,free,present,Option.map_some])
      (locate_right reached record other.tree)
    simpa only [write_join_right] using actual
  | copy instruction =>
    rename_i destination origin
    have destinationFree := unused destination (by simp [instruction,Instruction.targets])
    have originFree := unused origin (by simp [instruction,Instruction.targets])
    rw [← copy_join_right record other before destination origin destinationFree originFree]
    exact .copy instruction

end TangoSquared.Paper20261030.MultiSourceProgram
