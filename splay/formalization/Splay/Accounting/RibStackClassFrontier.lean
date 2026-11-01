import Splay.Accounting.RibStackOperations
import Splay.Accounting.RibStackFoldingWord

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree OfflineConnectedSupport Digits

/-- The class spine with a fixed arbitrary terminal subtree. Keeping this
terminal explicit permits cutting off the upper folded chunks without
pretending that the remaining hole is an empty tree. -/
inductive ClassFrontier {terminalLower upper : ℕ} (terminal : BST terminalLower upper) :
    {lower : ℕ} → ℕ → List Digit → SupportFrontier lower upper → Prop
  | empty (level : ℕ) : ClassFrontier terminal level [] (.last terminal)
  | one {level lower root : ℕ} {digits : List Digit}
      {a : BST lower root} {tail : SupportFrontier (root + 1) upper}
      (first : ClassTree level a) (rest : ClassFrontier terminal (level + 1) digits tail) :
      ClassFrontier terminal level (.one :: digits) (.next a tail)
  | two {level lower x y : ℕ} {digits : List Digit}
      {a : BST lower x} {b : BST (x + 1) y} {tail : SupportFrontier (y + 1) upper}
      (first : ClassTree level a) (second : ClassTree level b)
      (rest : ClassFrontier terminal (level + 1) digits tail) :
      ClassFrontier terminal level (.two :: digits) (.next a (.next b tail))
  | three {level lower x y z : ℕ} {digits : List Digit}
      {a : BST lower x} {b : BST (x + 1) y} {c : BST (y + 1) z}
      {tail : SupportFrontier (z + 1) upper}
      (first : ClassTree level a) (second : ClassTree level b) (third : ClassTree level c)
      (rest : ClassFrontier terminal (level + 1) digits tail) :
      ClassFrontier terminal level (.three :: digits) (.next a (.next b (.next c tail)))

namespace ClassFrontier

theorem card {terminalLower lower upper level : ℕ} {terminal : BST terminalLower upper}
    {digits : List Digit} {frontier : SupportFrontier lower upper}
    (classes : ClassFrontier terminal level digits frontier) : frontier.card = spineNodes digits := by
  induction classes with
  | empty => rfl
  | one first rest ih => simp [SupportFrontier.card, spineNodes_cons, Digit.value, ih]; omega
  | two first second rest ih => simp [SupportFrontier.card, spineNodes_cons, Digit.value, ih]; omega
  | three first second third rest ih => simp [SupportFrontier.card, spineNodes_cons, Digit.value, ih]; omega

theorem exists_push_unfolded {terminalLower lower root upper level : ℕ}
    {terminal : BST terminalLower upper} {digits : List Digit}
    {left : BST lower root} {frontier : SupportFrontier (root + 1) upper}
    (classes : ClassFrontier terminal level digits frontier) (newClass : ClassTree level left) :
    ∃ result : SupportFrontier lower upper,
      ClassFrontier terminal level (Digits.push digits) result ∧
      HasSupportedPath (.node left frontier.tree) result.tree
        (16 * pushCost level digits) (16 * pushCost level digits) := by
  induction digits generalizing level lower root with
  | nil =>
      cases classes
      exact ⟨_, .one newClass (.empty _), (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
  | cons digit digits ih =>
      cases classes with
      | one first rest =>
          exact ⟨_, .two newClass first rest, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
      | two first second rest =>
          exact ⟨_, .three newClass first second rest, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
      | three first second third rest =>
          rename_i b c tail a
          obtain ⟨result, shaped, carry⟩ := ih rest (ClassTree.join b c second third)
          obtain ⟨ja, jb, joined, _, support, cost⟩ := exists_classJoin_path second third
          have joinPath : HasSupportedPath (.node b c)
              (.node (pullMin b).tree (pullMax c).tree) (4 * level + 1) (4 * level) :=
            ⟨ja, jb, joined, support, cost⟩
          have step := ((HasSupportedPath.rootLeft b c tail.tree).trans (joinPath.leftContext tail.tree)).trans carry
          refine ⟨_, .two newClass first shaped, ((step.rightContext a).rightContext left).mono ?_ ?_⟩
          · simp only [pushCost]; omega
          · simp only [pushCost]; omega

theorem exists_pop_unfolded {terminalLower lower upper level : ℕ}
    {terminal : BST terminalLower upper} {digits : List Digit}
    {frontier : SupportFrontier lower upper}
    (classes : ClassFrontier terminal level digits frontier) (nonempty : digits ≠ []) :
    ∃ (root : ℕ) (left : BST lower root) (result : SupportFrontier (root + 1) upper),
      ClassTree level left ∧ ClassFrontier terminal level (Digits.pop digits) result ∧
      HasSupportedPath frontier.tree (.node left result.tree)
        (16 * popCost level digits) (16 * popCost level digits) := by
  induction classes with
  | empty => exact False.elim (nonempty rfl)
  | @one level lo x digits a tail first rest ih =>
      cases digits with
      | nil =>
          cases rest
          exact ⟨_, a, _, first, .empty _, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
      | cons digit digits =>
          obtain ⟨root, borrowed, remainder, borrowedClass, remainderShape, borrow⟩ := ih (by simp)
          obtain ⟨key, b, c, classB, classC, ua, ub, unjoined, _, support, cost⟩ :=
            borrowedClass.exists_unjoin_path
          have unjoinPath : HasSupportedPath borrowed (.node b c) (4 * level + 1) (4 * level) :=
            ⟨ua, ub, unjoined, support, cost⟩
          have step := (borrow.trans (unjoinPath.leftContext remainder.tree)).trans
            (HasSupportedPath.rootRight b c remainder.tree)
          refine ⟨_, a, _, first, .two classB classC remainderShape, (step.rightContext a).mono ?_ ?_⟩
          · simp only [popCost]; omega
          · simp only [popCost]; omega
  | two first second rest ih =>
      exact ⟨_, _, _, first, .one second rest, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩
  | three first second third rest ih =>
      exact ⟨_, _, _, first, .two second third rest, (HasSupportedPath.refl _).mono (by omega) (by omega)⟩

end ClassFrontier

end Splay.Accounting.OfflineNormalForm.RibStack
