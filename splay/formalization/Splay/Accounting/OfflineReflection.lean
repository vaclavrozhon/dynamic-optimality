import Splay.Accounting.OfflineSupportedComposition

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree Splay.Tree.BST OfflineNormalForm

/-- Order reversal with explicit interval indices. This avoids arithmetic
casts at every rotation when transferring a minimum stack to a maximum stack. -/
inductive Reflection : {beforeLower beforeUpper afterLower afterUpper : ℕ} →
    BST beforeLower beforeUpper → BST afterLower afterUpper → Type
  | leaf (before after : ℕ) : Reflection (.empty before) (.empty after)
  | node {beforeLower beforeRoot beforeUpper afterLower afterRoot afterUpper : ℕ}
      {left : BST beforeLower beforeRoot} {right : BST (beforeRoot + 1) beforeUpper}
      {leftImage : BST (afterRoot + 1) afterUpper} {rightImage : BST afterLower afterRoot}
      (leftReflection : Reflection left leftImage) (rightReflection : Reflection right rightImage) :
      Reflection (.node left right) (.node rightImage leftImage)

namespace Reflection

def restrict : {beforeLower beforeUpper afterLower afterUpper : ℕ} →
    {before : BST beforeLower beforeUpper} → {after : BST afterLower afterUpper} →
    Reflection before after → RootPrefix before → RootPrefix after
  | _, _, _, _, _, _, .leaf _ _, .none _ => .none _
  | _, _, _, _, _, _, .node _ _, .none _ => .none _
  | _, _, _, _, _, _, .node left right, .node a b => .node (right.restrict b) (left.restrict a)

theorem restrict_card {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) (selected : RootPrefix before) :
    (reflection.restrict selected).card = selected.card := by
  induction reflection with
  | leaf => cases selected; rfl
  | node left right ihL ihR =>
      cases selected with
      | none => rfl
      | node a b => simp only [restrict, RootPrefix.card, ihL, ihR]; omega

theorem size_eq {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) : after.size = before.size := by
  induction reflection with
  | leaf => rfl
  | node left right ihL ihR => simp only [BST.size, ihL, ihR]; omega

theorem height_eq {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) : after.height = before.height := by
  induction reflection with
  | leaf => rfl
  | node left right ihL ihR => simp [BST.height, ihL, ihR, Nat.max_comm]

theorem boundary_eq {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) :
    leftBoundaryDepth after = rightBoundaryDepth before ∧
      rightBoundaryDepth after = leftBoundaryDepth before := by
  induction reflection with
  | leaf => exact ⟨rfl, rfl⟩
  | node left right ihL ihR => simp [leftBoundaryDepth, rightBoundaryDepth, ihL, ihR]

theorem ribs_iff {beforeLower beforeUpper afterLower afterUpper slack : ℕ}
    {before : BST beforeLower beforeUpper} {after : BST afterLower afterUpper}
    (reflection : Reflection before after) :
    HasBoundedMinorRibs after slack ↔ HasBoundedMinorRibs before slack := by
  induction reflection with
  | leaf => rfl
  | node left right ihL ihR =>
      have leftBoundary := left.boundary_eq
      have rightBoundary := right.boundary_eq
      simp only [HasBoundedMinorRibs, leftBoundary, rightBoundary, ihL, ihR]
      tauto

theorem exists_image {beforeLower beforeUpper : ℕ}
    (before : BST beforeLower beforeUpper) (lower : ℕ) :
    ∃ (upper : ℕ) (after : BST lower upper), Nonempty (Reflection before after) ∧ upper = lower + before.size := by
  induction before generalizing lower with
  | empty boundary => exact ⟨lower, .empty lower, ⟨.leaf boundary lower⟩, by simp [BST.size]⟩
  | node left right ihL ihR =>
      obtain ⟨root, rightImage, ⟨rightReflection⟩, rightSize⟩ := ihR lower
      obtain ⟨upper, leftImage, ⟨leftReflection⟩, leftSize⟩ := ihL (root + 1)
      exact ⟨upper, .node rightImage leftImage, ⟨.node leftReflection rightReflection⟩,
        by simp only [BST.size]; omega⟩

theorem exists_image_exact {beforeLower beforeUpper : ℕ}
    (before : BST beforeLower beforeUpper) (lower : ℕ) :
    ∃ after : BST lower (lower + before.size), Nonempty (Reflection before after) := by
  obtain ⟨upper, after, reflection, same⟩ := exists_image before lower
  subst upper
  exact ⟨after, reflection⟩

end Reflection

theorem SupportedRotation.reflect
    {beforeLower beforeUpper afterLower afterUpper depth : ℕ}
    {before after : BST beforeLower beforeUpper} {imageBefore : BST afterLower afterUpper}
    {rotation : RotationAt depth before after} {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) (reflection : Reflection before imageBefore) :
    ∃ (imageAfter : BST afterLower afterUpper) (result : Reflection after imageAfter)
      (imageRotation : RotationAt depth imageBefore imageAfter),
      SupportedRotation imageRotation (reflection.restrict a) (result.restrict b) := by
  induction supported generalizing afterLower afterUpper with
  | rootLeft a b c pa pb pc =>
      cases reflection with
      | node left rest =>
          cases rest with
          | node middle right =>
              exact ⟨_, .node (.node left middle) right, .root (.right _ _ _), .rootRight _ _ _ _ _ _⟩
  | rootRight a b c pa pb pc =>
      cases reflection with
      | node rest right =>
          cases rest with
          | node left middle =>
              exact ⟨_, .node left (.node middle right), .root (.left _ _ _), .rootLeft _ _ _ _ _ _⟩
  | leftContext rotation supported right selectedRight ih =>
      cases reflection with
      | node left right =>
          obtain ⟨imageAfter, result, imageRotation, supported⟩ := ih left
          exact ⟨_, .node result right, .rightContext _ imageRotation,
            .rightContext _ _ imageRotation supported⟩
  | rightContext left selectedLeft rotation supported ih =>
      cases reflection with
      | node left right =>
          obtain ⟨imageAfter, result, imageRotation, supported⟩ := ih right
          exact ⟨_, .node left result, .leftContext imageRotation _,
            .leftContext imageRotation supported _ _⟩

theorem SupportedPath.reflect
    {beforeLower beforeUpper afterLower afterUpper : ℕ}
    {before after : BST beforeLower beforeUpper} {imageBefore : BST afterLower afterUpper}
    {a : RootPrefix before} {b : RootPrefix after}
    (path : SupportedPath a b) (reflection : Reflection before imageBefore) :
    ∃ (imageAfter : BST afterLower afterUpper) (result : Reflection after imageAfter)
      (imagePath : SupportedPath (reflection.restrict a) (result.restrict b)),
      imagePath.length = path.length ∧ (∀ bound, imagePath.DepthBound bound ↔ path.DepthBound bound) := by
  induction path generalizing afterLower afterUpper with
  | nil selected => exact ⟨_, reflection, .nil _, rfl, fun _ => Iff.rfl⟩
  | cons rotation supported tail ih =>
      obtain ⟨middle, middleReflection, imageRotation, supportedImage⟩ := supported.reflect reflection
      obtain ⟨imageAfter, result, imageTail, length, depths⟩ := ih middleReflection
      exact ⟨imageAfter, result, .cons imageRotation supportedImage imageTail,
        by simp [SupportedPath.length, length],
        by intro bound; simp only [SupportedPath.DepthBound, depths bound]⟩

theorem HasSupportedPath.reflect
    {beforeLower beforeUpper afterLower afterUpper support rotations : ℕ}
    {before after : BST beforeLower beforeUpper} {imageBefore : BST afterLower afterUpper}
    (path : HasSupportedPath before after support rotations) (reflection : Reflection before imageBefore) :
    ∃ imageAfter : BST afterLower afterUpper, Nonempty (Reflection after imageAfter) ∧
      HasSupportedPath imageBefore imageAfter support rotations := by
  obtain ⟨a, b, path, card, cost⟩ := path
  obtain ⟨imageAfter, result, imagePath, length, _⟩ := path.reflect reflection
  exact ⟨imageAfter, ⟨result⟩, _, _, imagePath, by simpa [Reflection.restrict_card] using card, by omega⟩

end Splay.Accounting.OfflineConnectedSupport
