import Splay.Accounting.RibStackClasses
import Splay.Accounting.RibStackDigits
import Splay.Accounting.OfflineSupportedComposition

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport
open Digits

/-- The unfolded stack, with its actual class trees and exact class counter.
The final external leaf is represented by the empty tree at its true bound. -/
inductive StackShape : {lower upper : ℕ} → ℕ → List Digit → BST lower upper → Prop
  | empty (level boundary : ℕ) : StackShape level [] (.empty boundary)
  | one {level lower x upper : ℕ} {digits : List Digit}
      {a : BST lower x} {tail : BST (x + 1) upper}
      (first : ClassTree level a) (rest : StackShape (level + 1) digits tail) :
      StackShape level (.one :: digits) (.node a tail)
  | two {level lower x y upper : ℕ} {digits : List Digit}
      {a : BST lower x} {b : BST (x + 1) y} {tail : BST (y + 1) upper}
      (first : ClassTree level a) (second : ClassTree level b)
      (rest : StackShape (level + 1) digits tail) :
      StackShape level (.two :: digits) (.node a (.node b tail))
  | three {level lower x y z upper : ℕ} {digits : List Digit}
      {a : BST lower x} {b : BST (x + 1) y} {c : BST (y + 1) z}
      {tail : BST (z + 1) upper}
      (first : ClassTree level a) (second : ClassTree level b) (third : ClassTree level c)
      (rest : StackShape (level + 1) digits tail) :
      StackShape level (.three :: digits) (.node a (.node b (.node c tail)))

namespace StackShape

theorem size {level lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (stacked : StackShape level digits tree) : tree.size = 2 ^ level * value digits := by
  induction stacked with
  | empty => simp [BST.size, value]
  | one first rest ih =>
      have size := first.size_add_one
      simp only [BST.size, value, Digit.value, pow_succ] at *
      nlinarith
  | two first second rest ih =>
      have sizeA := first.size_add_one
      have sizeB := second.size_add_one
      simp only [BST.size, value, Digit.value, pow_succ] at *
      nlinarith
  | three first second third rest ih =>
      have sizeA := first.size_add_one
      have sizeB := second.size_add_one
      have sizeC := third.size_add_one
      simp only [BST.size, value, Digit.value, pow_succ] at *
      nlinarith

theorem height_le {level lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (stacked : StackShape level digits tree) : tree.height ≤ 2 * level + 5 * digits.length := by
  induction stacked with
  | empty => simp [BST.height]
  | one first rest ih =>
      have height := first.height_le
      simp only [BST.height, List.length_cons]
      omega
  | two first second rest ih =>
      have heightA := first.height_le
      have heightB := second.height_le
      simp only [BST.height, List.length_cons]
      omega
  | three first second third rest ih =>
      have heightA := first.height_le
      have heightB := second.height_le
      have heightC := third.height_le
      simp only [BST.height, List.length_cons]
      omega

/-- Before folding, only the right outer spine may be long. -/
theorem geometry {level lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (stacked : StackShape level digits tree) :
    HasBoundedMinorRibs tree 4 ∧ leftBoundaryDepth tree ≤ 3 := by
  have nodeGeometry {lo key hi : ℕ} {left : BST lo key} {right : BST (key + 1) hi}
      (leftGeometry : HasBoundedMinorRibs left 4 ∧
        leftBoundaryDepth left ≤ 2 ∧ rightBoundaryDepth left ≤ 2)
      (rightGeometry : HasBoundedMinorRibs right 4 ∧ leftBoundaryDepth right ≤ 3) :
      HasBoundedMinorRibs (.node left right) 4 ∧ leftBoundaryDepth (.node left right) ≤ 3 :=
    ⟨⟨by omega, by omega, leftGeometry.1, rightGeometry.1⟩, by
      simp only [leftBoundaryDepth]
      omega⟩
  induction stacked with
  | empty => simp [HasBoundedMinorRibs, leftBoundaryDepth]
  | one first rest ih => exact nodeGeometry first.geometry ih
  | two first second rest ih => exact nodeGeometry first.geometry (nodeGeometry second.geometry ih)
  | three first second third rest ih =>
      exact nodeGeometry first.geometry (nodeGeometry second.geometry (nodeGeometry third.geometry ih))

theorem height_le_log {lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (stacked : StackShape 0 digits tree) : tree.height ≤ 5 * Nat.clog 2 (tree.size + 1) := by
  have height := stacked.height_le
  have length := length_le_clog digits
  have size := stacked.size
  simp only [pow_zero, one_mul] at size
  rw [size]
  omega

/-- A push assimilates a real joining node and its class-`level` left child.
Both charged support and rotations follow the already amortized counter. -/
theorem exists_push {level lower root upper : ℕ} {digits : List Digit}
    {left : BST lower root} {tree : BST (root + 1) upper}
    (stacked : StackShape level digits tree) (newClass : ClassTree level left) :
    ∃ result : BST lower upper, StackShape level (Digits.push digits) result ∧
      HasSupportedPath (.node left tree) result
        (16 * pushCost level digits) (16 * pushCost level digits) := by
  induction digits generalizing level lower root upper with
  | nil =>
      cases stacked with
      | empty =>
          exact ⟨_, .one newClass (.empty _ _),
            (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
  | cons digit digits ih =>
      cases stacked with
      | one first rest =>
          exact ⟨_, .two newClass first rest,
            (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
      | two first second rest =>
          exact ⟨_, .three newClass first second rest,
            (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
      | three first second third rest =>
          rename_i b c a tail
          obtain ⟨result, resultShape, carry⟩ := ih rest (ClassTree.join b c second third)
          obtain ⟨ja, jb, joined, _, joinSupport, joinCost⟩ := exists_classJoin_path second third
          have joinPath : HasSupportedPath (.node b c)
              (.node (pullMin b).tree (pullMax c).tree) (4 * level + 1) (4 * level) :=
            ⟨ja, jb, joined, joinSupport, joinCost⟩
          have step := ((HasSupportedPath.rootLeft b c tail).trans (joinPath.leftContext tail)).trans carry
          have lifted := (step.rightContext a).rightContext left
          refine ⟨_, .two newClass first resultShape, lifted.mono ?_ ?_⟩
          · simp only [pushCost]
            omega
          · simp only [pushCost]
            omega

/-- Pop exposes the first class tree and normalizes the remaining real BST.
At level zero this is precisely the stack API's empty-left-child root. -/
theorem exists_pop {level lower upper : ℕ} {digits : List Digit} {tree : BST lower upper}
    (stacked : StackShape level digits tree) (nonempty : digits ≠ []) :
    ∃ (root : ℕ) (left : BST lower root) (result : BST (root + 1) upper),
      ClassTree level left ∧ StackShape level (Digits.pop digits) result ∧
      HasSupportedPath tree (.node left result)
        (16 * popCost level digits) (16 * popCost level digits) := by
  induction stacked with
  | empty => exact False.elim (nonempty rfl)
  | @one level lo x hi digits a tail first rest ih =>
      cases digits with
      | nil =>
          cases rest
          exact ⟨_, a, _, first, .empty _ _,
            (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
      | cons digit digits =>
          obtain ⟨root, borrowed, remainder, borrowedClass, remainderShape, borrow⟩ := ih (by simp)
          obtain ⟨key, b, c, classB, classC, ua, ub, unjoined, _, unjoinSupport, unjoinCost⟩ :=
            borrowedClass.exists_unjoin_path
          have unjoinPath : HasSupportedPath borrowed (.node b c)
              (4 * level + 1) (4 * level) := ⟨ua, ub, unjoined, unjoinSupport, unjoinCost⟩
          have step := (borrow.trans (unjoinPath.leftContext remainder)).trans
            (HasSupportedPath.rootRight b c remainder)
          have lifted := step.rightContext a
          refine ⟨_, a, _, first, .two classB classC remainderShape, lifted.mono ?_ ?_⟩
          · simp only [popCost]
            omega
          · simp only [popCost]
            omega
  | two first second rest ih =>
      exact ⟨_, _, _, first, .one second rest,
        (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
  | three first second third rest ih =>
      exact ⟨_, _, _, first, .two second third rest,
        (HasSupportedPath.refl _).mono (by omega) (by omega)⟩

end StackShape

end Splay.Accounting.OfflineNormalForm.RibStack
