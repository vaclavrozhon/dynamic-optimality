import TangoSquared.Paper20261030.SourceFingerExtension
import TangoSquared.Paper20261030.PackedContext

/-! Joining two disjoint physical pieces below one connector. A finger
in the left piece receives a left prefix, and one in the right receives
a right prefix. The left choice takes precedence; applications use
disjoint finger sets. Connector construction and initial pointer setup
are separate from this semantic embedding.
-/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions
open DynamicOptimality.LocalProgram (Move)

variable {α ρ F : Type*} [DecidableEq F]

def join (record : ρ) (left right : Configuration F α ρ) : Configuration F α ρ :=
  ⟨.fork record left.tree right.tree,fun finger => match left.fingers finger with
    | some position => some (false::position)
    | none => (right.fingers finger).map (true::·)⟩

theorem extend_left_tree (current : Cursor α ρ) (record : ρ) (sibling : Source α ρ) :
    (current.extend [.left record sibling]).tree = .fork record current.tree sibling := by
  change plug current.focus (current.ancestors++[.left record sibling]) = _
  rw [plug_append]
  rfl

theorem extend_right_tree (current : Cursor α ρ) (record : ρ) (sibling : Source α ρ) :
    (current.extend [.right sibling record]).tree = .fork record sibling current.tree := by
  change plug current.focus (current.ancestors++[.right sibling record]) = _
  rw [plug_append]
  rfl

theorem join_wellFormed (record : ρ) (left right : Configuration F α ρ)
    (leftValid : WellFormed left) (rightValid : WellFormed right) : WellFormed (join record left right) := by
  intro finger position present
  cases location : left.fingers finger with
  | some original =>
    have equal : false::original = position := by simpa only [join,location,Option.some.injEq] using present
    subst position
    obtain ⟨current,reached⟩ := leftValid finger original location
    exact ⟨_,locate_left reached record right.tree⟩
  | none =>
    cases rightLocation : right.fingers finger with
    | none => simp only [join,location,rightLocation,Option.map_none,reduceCtorEq] at present
    | some original =>
      have equal : true::original = position := by simpa only [join,location,rightLocation,Option.map_some,Option.some.injEq] using present
      subst position
      obtain ⟨current,reached⟩ := rightValid finger original rightLocation
      exact ⟨_,locate_right reached record left.tree⟩

theorem move_join_left (record : ρ) (left right : Configuration F α ρ) (finger : F)
    (action : Move) (before after : Cursor α ρ) :
    moveResult (join record left right) finger action (before.extend [.left record right.tree]) (after.extend [.left record right.tree]) =
      join record (moveResult left finger action before after) right := by
  apply congrArg₂ Configuration.mk
  · exact extend_left_tree after record right.tree
  · funext other
    by_cases same : other = finger
    · subst other
      simp [moveResult,join,address_extend,direction]
    · simp only [moveResult,join,Function.update_of_ne same,transport_extend,underContext,direction]
      cases location : left.fingers other with
      | none => cases right.fingers other <;> simp [underChild]
      | some position => simp [underChild]

theorem move_join_right (record : ρ) (left right : Configuration F α ρ) (finger : F)
    (free : left.fingers finger = none) (action : Move) (before after : Cursor α ρ) :
    moveResult (join record left right) finger action (before.extend [.right left.tree record]) (after.extend [.right left.tree record]) =
      join record left (moveResult right finger action before after) := by
  apply congrArg₂ Configuration.mk
  · exact extend_right_tree after record left.tree
  · funext other
    by_cases same : other = finger
    · subst other
      simp [moveResult,join,free,address_extend,direction]
    · simp only [moveResult,join,Function.update_of_ne same,transport_extend,underContext,direction]
      cases location : left.fingers other with
      | none => cases right.fingers other <;> simp [underChild]
      | some position => simp [underChild]

theorem write_join_left (record : ρ) (left right : Configuration F α ρ) (current : Cursor α ρ) (fresh : ρ) :
    writeResult (join record left right) (current.extend [.left record right.tree]) fresh =
      join record (writeResult left current fresh) right := by
  apply congrArg₂ Configuration.mk
  · change plug (current.focus.setRoot fresh) (current.ancestors++[.left record right.tree]) = _
    rw [plug_append]
    rfl
  · rfl

theorem write_join_right (record : ρ) (left right : Configuration F α ρ) (current : Cursor α ρ) (fresh : ρ) :
    writeResult (join record left right) (current.extend [.right left.tree record]) fresh =
      join record left (writeResult right current fresh) := by
  apply congrArg₂ Configuration.mk
  · change plug (current.focus.setRoot fresh) (current.ancestors++[.right left.tree record]) = _
    rw [plug_append]
    rfl
  · rfl

end TangoSquared.Paper20261030.MultiSourceProgram
