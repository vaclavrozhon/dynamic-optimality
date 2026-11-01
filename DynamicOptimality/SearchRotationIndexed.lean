import DynamicOptimality.SearchRotationModel
import Splay.Tree.RotationDepthBound

/-! # Exact representation bridges for search and arbitrary rotations -/

namespace DynamicOptimality.SearchRotation

open TangoSquared.MTR

theorem toRaw_searchDepth {lower upper key : Nat} (tree : BST lower upper)
    (insideLower : lower ≤ key) (insideUpper : key < upper) :
    Tree.searchDepth key tree.toRaw = some (tree.depth key) := by
  induction tree with
  | empty boundary => omega
  | @node lower root upper left right ihLeft ihRight =>
    by_cases hLeft : key < root
    · have hNe : key ≠ root := by omega
      simp [BST.toRaw, Tree.searchDepth, Splay.Tree.BST.depth, hLeft, hNe,
        ihLeft insideLower hLeft]
    · by_cases hRight : root < key
      · have hNe : key ≠ root := by omega
        simp [BST.toRaw, Tree.searchDepth, Splay.Tree.BST.depth, hLeft, hRight, hNe,
          ihRight (by omega) insideUpper]
      · have hEq : key = root := by omega
        subst key
        simp [BST.toRaw, Tree.searchDepth, Splay.Tree.BST.depth]

/-- Erasure of a rotation preserves its actual location and orientation. -/
theorem rotation_toRaw {depth lower upper : Nat} {before after : BST lower upper}
    (step : Splay.Tree.BST.RotationAt depth before after) :
    Rotation before.toRaw after.toRaw := by
  induction step with
  | root step =>
    cases step with
    | right a b c => exact .rootRight (BST.toRaw a) (BST.toRaw b) (BST.toRaw c) _ _
    | left a b c => exact .rootLeft (BST.toRaw a) (BST.toRaw b) (BST.toRaw c) _ _
  | leftContext step right ih => exact .leftContext ih _ (BST.toRaw right)
  | rightContext left step ih => exact .rightContext (BST.toRaw left) _ ih

/-- Every raw rotation of an indexed tree lifts to an indexed rotation. -/
theorem rotation_lift {a b : RawTree Nat} (step : Rotation a b)
    {lower upper : Nat} (tree : BST lower upper) (same : tree.toRaw = a) :
    ∃ (after : BST lower upper) (depth : Nat),
      Splay.Tree.BST.RotationAt depth tree after ∧ after.toRaw = b := by
  induction step generalizing lower upper with
  | rootRight a b c x y =>
    cases tree with
    | empty => contradiction
    | node l r =>
      cases l with
      | empty => cases same
      | node ll lr =>
        simp only [BST.toRaw, Tree.node.injEq] at same
        rcases same with ⟨⟨ha,rfl,hb⟩,rfl,hc⟩
        exact ⟨.node ll (.node lr r), 0, .root (.right ll lr r),
          by simp [BST.toRaw, ha, hb, hc]⟩
  | rootLeft a b c x y =>
    cases tree with
    | empty => contradiction
    | node l r =>
      cases r with
      | empty => cases same
      | node rl rr =>
        simp only [BST.toRaw, Tree.node.injEq] at same
        rcases same with ⟨ha,rfl,⟨hb,rfl,hc⟩⟩
        exact ⟨.node (.node l rl) rr, 0, .root (.left l rl rr),
          by simp [BST.toRaw, ha, hb, hc]⟩
  | leftContext step key right ih =>
    cases tree with
    | empty => contradiction
    | node l r =>
      simp only [BST.toRaw, Tree.node.injEq] at same
      rcases same with ⟨hl, rfl, hr⟩
      obtain ⟨l', depth, lifted, same'⟩ := ih l hl
      exact ⟨.node l' r, depth + 1, .leftContext lifted r,
        by simp [BST.toRaw, same', hr]⟩
  | rightContext left key step ih =>
    cases tree with
    | empty => contradiction
    | node l r =>
      simp only [BST.toRaw, Tree.node.injEq] at same
      rcases same with ⟨hl, rfl, hr⟩
      obtain ⟨r', depth, lifted, same'⟩ := ih r hr
      exact ⟨.node l r', depth + 1, .rightContext l lifted,
        by simp [BST.toRaw, same', hl]⟩

theorem rotations_toRaw {count lower upper : Nat} {before after : BST lower upper}
    (trace : Splay.Tree.BST.RotationExecution count before after) :
    Rotations before.toRaw after.toRaw count := by
  induction trace with
  | refl => exact .refl _
  | step head tail ih => exact .step (rotation_toRaw head) ih

theorem rotations_lift {a b : RawTree Nat} {count : Nat} (trace : Rotations a b count)
    {lower upper : Nat} (tree : BST lower upper) (same : tree.toRaw = a) :
    ∃ after : BST lower upper,
      Splay.Tree.BST.RotationExecution count tree after ∧ after.toRaw = b := by
  induction trace generalizing lower upper with
  | refl => exact ⟨tree, .refl, same⟩
  | step head tail ih =>
    obtain ⟨middle, depth, lifted, sameMiddle⟩ := rotation_lift head tree same
    obtain ⟨after, rest, sameAfter⟩ := ih middle sameMiddle
    exact ⟨after, .step lifted rest, sameAfter⟩

/-- Internal key depth is the odd-position instance of external depth. -/
theorem externalDepth_key {lower upper : Nat} (tree : BST lower upper) (key : Nat) :
    tree.externalDepth (2 * key + 1) = tree.depth key := by
  induction tree with
  | empty => rfl
  | @node lower root upper left right ihLeft ihRight =>
    by_cases hEq : key = root
    · subst key
      simp
    · by_cases hLeft : key < root
      · have hPosition : 2 * key + 1 < 2 * root + 1 := by omega
        simp [Splay.Tree.BST.externalDepth, Splay.Tree.BST.depth, hEq, hLeft,
          hPosition, ihLeft]
      · have hPosition : ¬ 2 * key + 1 < 2 * root + 1 := by omega
        have hPositionNe : 2 * key + 1 ≠ 2 * root + 1 := by omega
        simp [Splay.Tree.BST.externalDepth, Splay.Tree.BST.depth, hEq, hLeft,
          hPosition, hPositionNe, ihRight]

theorem rotation_depth_within_one {depth lower upper : Nat}
    {before after : BST lower upper}
    (step : Splay.Tree.BST.RotationAt depth before after) (key : Nat) :
    after.depth key ≤ before.depth key + 1 ∧ before.depth key ≤ after.depth key + 1 := by
  simpa only [externalDepth_key] using step.externalDepth_within_one (2 * key + 1)

theorem rotations_depth_le {count lower upper : Nat} {before after : BST lower upper}
    (trace : Splay.Tree.BST.RotationExecution count before after) (key : Nat) :
    before.depth key ≤ after.depth key + count := by
  induction trace with
  | refl => omega
  | step head tail ih =>
    have bound := (rotation_depth_within_one head key).2
    omega

theorem rotations_symm {count lower upper : Nat} {before after : BST lower upper}
    (trace : Splay.Tree.BST.RotationExecution count before after) :
    Splay.Tree.BST.RotationExecution count after before := by
  induction trace with
  | refl => exact .refl
  | step head tail ih => exact ih.append (.singleton head.symm)

end DynamicOptimality.SearchRotation
