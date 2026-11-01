import Splay.Tree.SplayHitNodes
import Splay.Lazy.Model

namespace Splay.Accounting

open Splay.Tree.BST

/--
Side of the accessed root-heavy path on which the two light children of a
proper search ancestor lie.  An ancestor smaller than the access is passed
on its right branch, so both of its light children lie to the left of the
access; the other case is symmetric.
-/
def hitSide (key ancestor : ℕ) : Splay.Lazy.Side :=
  if ancestor < key then .left else .right

/--
The two bottom-up search ancestors consumed by an oriented double rotation,
together with the exact equality test on their lazy-interval sides.

This is the list-level form of the manuscript distinction: a zig-zig uses
two consecutive ancestor cells on the same side, whereas a zig-zag uses one
cell on each side.
-/
theorem DoubleOrientationAt.exists_first_two_hit_sides
    {flag : Bool} {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt flag
        (depth := depth) (key := key) before after) :
    ∃ first second rest,
      (before.searchPath key).dropLast.reverse =
          first :: second :: rest ∧
        (hitSide key first = hitSide key second ↔ flag = true) := by
  induction orientation with
  | @zigZigLeft lower first second third upper a b c d =>
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      refine ⟨second, third, [], ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show first ≠ third by omega, show first < third by omega,
          show first ≠ second by omega, firstLtSecond]
      · simp [hitSide, show ¬second < first by omega,
          show ¬third < first by omega]
  | @zigZigRight lower first second third upper a b c d =>
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      refine ⟨second, first, [], ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show third ≠ first by omega, show ¬third < first by omega,
          show third ≠ second by omega, show ¬third < second by omega]
      · simp [hitSide, show second < third by omega,
          show first < third by omega]
  | @zigZagLeftRight lower first second third upper a b c d =>
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      refine ⟨first, third, [], ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show second ≠ third by omega, show second < third by omega,
          show second ≠ first by omega, show ¬second < first by omega]
      · simp [hitSide, firstLtSecond, show ¬third < second by omega]
  | @zigZagRightLeft lower first second third upper a b c d =>
      have firstLtSecond : first < second := by
        have := b.lower_le_upper
        omega
      have secondLtThird : second < third := by
        have := c.lower_le_upper
        omega
      refine ⟨third, first, [], ?_, ?_⟩
      · simp [_root_.Splay.Tree.BST.searchPath,
          show second ≠ first by omega, show ¬second < first by omega,
          show second ≠ third by omega, show second < third by omega]
      · simp [hitSide, firstLtSecond, show ¬third < second by omega]
  | @leftContext flag depth key lower root upper before after
      orientation right ih =>
      obtain ⟨first, second, rest, innerPath, sides⟩ := ih
      have keyBounds := doubleOrientationAt_key_bounds orientation
      rw [searchPath.properAncestors_leftContext before right
        keyBounds.1 keyBounds.2]
      rw [innerPath]
      exact ⟨first, second, rest ++ [root], by simp, sides⟩
  | @rightContext flag depth key lower root upper left before after
      orientation ih =>
      obtain ⟨first, second, rest, innerPath, sides⟩ := ih
      have keyBounds := doubleOrientationAt_key_bounds orientation
      have rootLtKey : root < key := by omega
      rw [searchPath.properAncestors_rightContext left before
        rootLtKey keyBounds.2]
      rw [innerPath]
      exact ⟨first, second, rest ++ [root], by simp, sides⟩

theorem DoubleOrientationAt.first_two_hit_sides_eq_of_zigZig
    {depth key lower upper : ℕ} {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key) before after) :
    ∃ first second rest,
      (before.searchPath key).dropLast.reverse =
          first :: second :: rest ∧
        hitSide key first = hitSide key second := by
  obtain ⟨first, second, rest, path, sides⟩ :=
    orientation.exists_first_two_hit_sides
  exact ⟨first, second, rest, path, sides.mpr rfl⟩

theorem DoubleOrientationAt.first_two_hit_sides_ne_of_zigZag
    {depth key lower upper : ℕ} {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt false
        (depth := depth) (key := key) before after) :
    ∃ first second rest,
      (before.searchPath key).dropLast.reverse =
          first :: second :: rest ∧
        hitSide key first ≠ hitSide key second := by
  obtain ⟨first, second, rest, path, sides⟩ :=
    orientation.exists_first_two_hit_sides
  refine ⟨first, second, rest, path, ?_⟩
  intro equal
  exact Bool.noConfusion (sides.mp equal)

/-- Bottom-up sides of all proper search ancestors. -/
def hitSides {lower upper : ℕ} (tree : BST lower upper) (key : ℕ) :
    List Splay.Lazy.Side :=
  (tree.searchPath key).dropLast.reverse.map (hitSide key)

/-- Two heap children for every hit internal-node side. -/
def duplicateHitSides : List Splay.Lazy.Side → List Splay.Lazy.Side
  | [] => []
  | side :: sides => side :: side :: duplicateHitSides sides

@[simp]
theorem length_duplicateHitSides (sides : List Splay.Lazy.Side) :
    (duplicateHitSides sides).length = 2 * sides.length := by
  induction sides with
  | nil => rfl
  | cons side sides ih =>
      simp [duplicateHitSides, ih]
      omega

@[simp]
theorem duplicateHitSides_append
    (first second : List Splay.Lazy.Side) :
    duplicateHitSides (first ++ second) =
      duplicateHitSides first ++ duplicateHitSides second := by
  induction first with
  | nil => rfl
  | cons side sides ih =>
      simp [duplicateHitSides, ih]

/-- Reversing the cell order commutes with duplicating every cell side. -/
theorem reverse_duplicateHitSides (sides : List Splay.Lazy.Side) :
    (duplicateHitSides sides).reverse =
      duplicateHitSides sides.reverse := by
  induction sides with
  | nil => rfl
  | cons side sides ih =>
      simp [duplicateHitSides, ih, duplicateHitSides_append]

/--
Exact synchronization between the chronological splay transcript and the
two-child ancestor cells.  A zig consumes one cell, a zig-zig consumes two
equal-side cells, and a zig-zag consumes two opposite-side cells.
-/
inductive HitSideSchedule :
    List SplayStepKind → List Splay.Lazy.Side → Prop
  | done : HitSideSchedule [] []
  | zig {side} : HitSideSchedule [.zig] [side]
  | zigZig {kinds sides side} :
      HitSideSchedule kinds sides →
        HitSideSchedule (.zigZig :: kinds) (side :: side :: sides)
  | zigZag {kinds sides first second}
      (opposite : first ≠ second) :
      HitSideSchedule kinds sides →
        HitSideSchedule (.zigZag :: kinds) (first :: second :: sides)

namespace SplayExecutionTranscript

/-- Every concrete transcript has its exact side-cell schedule. -/
theorem hitSideSchedule
    {key lower upper : ℕ} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag) :
    HitSideSchedule kinds (hitSides before key) := by
  induction transcript with
  | done root =>
      have path := searchPath.eq_singleton_of_hasRoot root
      simp [hitSides, path, HitSideSchedule.done]
  | @zig lower upper before middle after kinds zig zigZig zigZag
      step tail tailTranscript ih =>
      have kindsNil :=
        tailTranscript.kinds_eq_nil_of_hasRoot_before step.hasRoot_after
      subst kinds
      obtain ⟨parent, beforePath, afterPath⟩ :=
        step.exists_searchPath_parent
      simpa [hitSides, beforePath, afterPath] using
        HitSideSchedule.zig (side := hitSide key parent)
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript ih =>
      obtain ⟨first, second, rest, beforeHits, sameSide⟩ :=
        orientation.first_two_hit_sides_eq_of_zigZig
      have restEq :
          rest = (middle.searchPath key).dropLast.reverse := by
        have dropped := SplayExecution.drop_two_hitNodes_of_double step
        rw [beforeHits] at dropped
        simpa using dropped
      simpa only [hitSides, beforeHits, List.map_cons, restEq, sameSide] using
        HitSideSchedule.zigZig ih
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript ih =>
      obtain ⟨first, second, rest, beforeHits, opposite⟩ :=
        orientation.first_two_hit_sides_ne_of_zigZag
      have restEq :
          rest = (middle.searchPath key).dropLast.reverse := by
        have dropped := SplayExecution.drop_two_hitNodes_of_double step
        rw [beforeHits] at dropped
        simpa using dropped
      simpa only [hitSides, beforeHits, List.map_cons, restEq] using
        HitSideSchedule.zigZag opposite ih

end SplayExecutionTranscript

end Splay.Accounting
