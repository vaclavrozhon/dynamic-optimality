import Splay.Accounting.RibStackPullMax
import Splay.Accounting.RibStackPullMin

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree
open OfflineConnectedSupport RestrictedSpines

@[simp] theorem pullMax_size {lower upper : ℕ} (tree : BST lower upper) :
    (pullMax tree).tree.size = tree.size := by
  have source := tree.size_add_lower_eq_upper
  have target := (pullMax tree).tree.size_add_lower_eq_upper
  omega

@[simp] theorem pullMin_size {lower upper : ℕ} (tree : BST lower upper) :
    (pullMin tree).tree.size = tree.size := by
  have source := tree.size_add_lower_eq_upper
  have target := (pullMin tree).tree.size_add_lower_eq_upper
  omega

/-- The canonical class trees used as crumbs of the ribless stack. -/
inductive ClassTree : {lower upper : ℕ} → ℕ → BST lower upper → Prop
  | zero (boundary : ℕ) : ClassTree 0 (.empty boundary)
  | join {level lower root upper : ℕ}
      (left : BST lower root) (right : BST (root + 1) upper)
      (leftClass : ClassTree level left) (rightClass : ClassTree level right) :
      ClassTree (level + 1) (.node (pullMin left).tree (pullMax right).tree)

namespace ClassTree

theorem size_add_one {level lower upper : ℕ} {tree : BST lower upper}
    (classed : ClassTree level tree) : tree.size + 1 = 2 ^ level := by
  induction classed with
  | zero => rfl
  | join left right leftClass rightClass ihL ihR =>
      simp only [BST.size, pullMin_size, pullMax_size, pow_succ]
      omega

theorem height_le {level lower upper : ℕ} {tree : BST lower upper}
    (classed : ClassTree level tree) : tree.height ≤ 2 * level := by
  induction classed with
  | zero => exact le_rfl
  | join left right leftClass rightClass ihL ihR =>
      have leftBound := pullMin_height_le left
      have rightBound := pullMax_height_le right
      simp only [BST.height]
      omega

/-- Uniform inward-rib slack four and at most one node on each outer spine.
The boundary depths here also count the root and final external edge. -/
theorem geometry {level lower upper : ℕ} {tree : BST lower upper}
    (classed : ClassTree level tree) :
    HasBoundedMinorRibs tree 4 ∧ leftBoundaryDepth tree ≤ 2 ∧ rightBoundaryDepth tree ≤ 2 := by
  induction classed with
  | zero => simp [HasBoundedMinorRibs, leftBoundaryDepth, rightBoundaryDepth]
  | join left right leftClass rightClass ihL ihR =>
      have leftSafe : InteriorSafe left 4 := ⟨ihL.1, by omega, by omega⟩
      have rightSafe : InteriorSafe right 4 := ⟨ihR.1, by omega, by omega⟩
      have leftBoundary := (pullMin left).leftBoundary_le_one
      have rightBoundary := (pullMax right).rightBoundary_le_one
      have leftInward := pullMin_rightBoundary_le left
      have rightInward := pullMax_leftBoundary_le right
      refine ⟨⟨by omega, by omega, pullMin_ribs leftSafe, pullMax_ribs rightSafe⟩, ?_, ?_⟩
      · simp only [leftBoundaryDepth]
        omega
      · simp only [rightBoundaryDepth]
        omega

end ClassTree

/-- Join two class-`level` trees with linear-in-level rotation and support
costs. The support records the two actual pull paths plus the joining root. -/
theorem exists_classJoin_path {level lower root upper : ℕ}
    {left : BST lower root} {right : BST (root + 1) upper}
    (leftClass : ClassTree level left) (rightClass : ClassTree level right) :
    ∃ (a : RootPrefix (BST.node left right))
      (b : RootPrefix (BST.node (pullMin left).tree (pullMax right).tree))
      (path : SupportedPath a b),
      0 < a.card ∧ a.card ≤ 4 * level + 1 ∧ path.length ≤ 4 * level := by
  obtain ⟨leftBefore, leftAfter, leftPath, leftCard, leftCost, leftEmpty⟩ := exists_pullMin_path left
  obtain ⟨rightBefore, rightAfter, rightPath, rightCard, rightCost, rightEmpty⟩ := exists_pullMax_path right
  have leftHeight := leftClass.height_le
  have rightHeight := rightClass.height_le
  refine ⟨.node leftBefore rightBefore, .node leftAfter rightAfter,
    (leftPath.leftContext rightBefore).append (rightPath.rightContext leftAfter), ?_, ?_, ?_⟩
  · simp only [RootPrefix.card]
    omega
  · simp only [RootPrefix.card]
    omega
  · simp only [SupportedPath.length_append, SupportedPath.length_leftContext,
      SupportedPath.length_rightContext]
    omega

/-- Unjoining reverses the exact class construction; it has the same bounds
and restores both class children, including their original tree shapes. -/
theorem ClassTree.exists_unjoin_path {level lower upper : ℕ} {tree : BST lower upper}
    (classed : ClassTree (level + 1) tree) :
    ∃ (root : ℕ) (left : BST lower root) (right : BST (root + 1) upper),
      ClassTree level left ∧ ClassTree level right ∧
      ∃ (a : RootPrefix tree) (b : RootPrefix (BST.node left right))
        (path : SupportedPath a b),
        0 < a.card ∧ a.card ≤ 4 * level + 1 ∧ path.length ≤ 4 * level := by
  cases classed with
  | join left right leftClass rightClass =>
      obtain ⟨a, b, path, positive, card, cost⟩ := exists_classJoin_path leftClass rightClass
      have same := path.toExecution.card_eq
      exact ⟨_, left, right, leftClass, rightClass, b, a, path.reverse,
        by omega, by omega, by simpa using cost⟩

end Splay.Accounting.OfflineNormalForm.RibStack
