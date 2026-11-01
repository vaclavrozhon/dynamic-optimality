import Splay.Accounting.OfflineSupportedPath

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree
open OfflineConnectedSupport RestrictedSpines

/-- A tree with its maximum key exposed and an empty right child. -/
inductive MaxExposed : ℕ → ℕ → Type
  | empty (boundary : ℕ) : MaxExposed boundary boundary
  | node {lower root : ℕ} (left : BST lower root) : MaxExposed lower (root + 1)

namespace MaxExposed

def tree : {lower upper : ℕ} → MaxExposed lower upper → BST lower upper
  | _, _, .empty boundary => BST.empty boundary
  | _, _, .node left => BST.node left (BST.empty _)

def inwardDepth {lower upper : ℕ} : MaxExposed lower upper → ℕ
  | .empty _ => 0
  | .node left => rightBoundaryDepth left

theorem rightBoundary_le_one {lower upper : ℕ} (exposed : MaxExposed lower upper) :
    rightBoundaryDepth exposed.tree ≤ 1 := by
  cases exposed <;> simp [tree, rightBoundaryDepth]

end MaxExposed

/-- Pull successive predecessors along one search path. In the recursive
right case the exposed maximum is rotated to the root; if it is already the
root, recurse into its left subtree. -/
def pullMax {lower upper : ℕ} : BST lower upper → MaxExposed lower upper
  | .empty boundary => .empty boundary
  | .node left right =>
      match pullMax right with
      | .empty _ => .node (pullMax left).tree
      | .node rightLeft => .node (.node left rightLeft)

theorem pullMax_height_le {lower upper : ℕ} (tree : BST lower upper) :
    (pullMax tree).tree.height ≤ tree.height + 1 := by
  induction tree with
  | empty => simp [pullMax, MaxExposed.tree, BST.height]
  | node left right ihL ihR =>
      generalize equation : pullMax right = exposed at *
      cases exposed with
      | empty =>
          simp only [pullMax, equation, MaxExposed.tree, BST.height] at *
          omega
      | node rightLeft =>
          simp only [pullMax, equation, MaxExposed.tree, BST.height] at *
          omega

theorem pullMax_leftBoundary_le {lower upper : ℕ} (tree : BST lower upper) :
    leftBoundaryDepth (pullMax tree).tree ≤ leftBoundaryDepth tree + 1 := by
  induction tree with
  | empty => simp [pullMax, MaxExposed.tree, leftBoundaryDepth]
  | node left right ihL ihR =>
      generalize equation : pullMax right = exposed at *
      cases exposed with
      | empty =>
          simp only [pullMax, equation, MaxExposed.tree, leftBoundaryDepth] at *
          omega
      | node rightLeft => simp [pullMax, equation, MaxExposed.tree, leftBoundaryDepth]

theorem pullMax_inwardDepth_le {lower upper : ℕ} (tree : BST lower upper) :
    (pullMax tree).inwardDepth ≤ rightBoundaryDepth tree := by
  induction tree with
  | empty => simp [pullMax, MaxExposed.inwardDepth, rightBoundaryDepth]
  | node left right ihL ihR =>
      generalize equation : pullMax right = exposed at *
      cases exposed with
      | empty =>
          have bound := (pullMax left).rightBoundary_le_one
          simp only [pullMax, equation, MaxExposed.inwardDepth, rightBoundaryDepth]
          omega
      | node rightLeft =>
          simp only [pullMax, equation, MaxExposed.inwardDepth, rightBoundaryDepth] at *
          omega

/-- Exposing a maximum preserves the rib bound when both original boundary
paths fit strictly within it. This is the invariant of the canonical class
trees; the resulting outer left boundary is allowed one extra node. -/
theorem pullMax_ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : InteriorSafe tree slack) : HasBoundedMinorRibs (pullMax tree).tree slack := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      have leftSafe := safe.left
      have rightSafe := safe.right
      have leftRibs := ihL leftSafe
      have rightRibs := ihR rightSafe
      have boundary := pullMax_leftBoundary_le right
      have inward := pullMax_inwardDepth_le (BST.node left right)
      have positive : 0 < slack := by have := safe.2.1; omega
      generalize equation : pullMax right = exposed at *
      cases exposed with
      | empty =>
          simp only [pullMax, equation, MaxExposed.tree, MaxExposed.inwardDepth] at inward ⊢
          refine ⟨Nat.succ_le_of_lt (lt_of_le_of_lt inward safe.2.2),
            by change 1 ≤ slack; omega, leftRibs, trivial⟩
      | node rightLeft =>
          simp only [pullMax, equation, MaxExposed.tree, MaxExposed.inwardDepth] at *
          refine ⟨?_, by change 1 ≤ slack; omega, ?_, trivial⟩
          · have := safe.2.2
            omega
          · refine ⟨safe.1.1, ?_, leftSafe.1, rightRibs.2.2.1⟩
            have original := safe.1.2.1
            simp only [leftBoundaryDepth] at boundary
            omega

/-- The pull operation has an actual supported path. Its support and rotation
count are both bounded by the original height, even for very large class trees. -/
theorem exists_pullMax_path {lower upper : ℕ} (tree : BST lower upper) :
    ∃ (a : RootPrefix tree) (b : RootPrefix (pullMax tree).tree) (path : SupportedPath a b),
      a.card ≤ tree.height ∧ path.length ≤ tree.height ∧
        (a.card = 0 → tree.size = 0) := by
  induction tree with
  | empty boundary => exact ⟨.none _, .none _, .nil _, le_rfl, le_rfl, fun _ => rfl⟩
  | @node lower root upper left right ihL ihR =>
      cases right with
      | empty =>
          obtain ⟨a, b, path, card, length, empty⟩ := ihL
          refine ⟨.node a (.none _), .node b (.none _), path.leftContext (.none _), ?_, ?_, ?_⟩
          · simp only [RootPrefix.card, BST.height]
            omega
          · change (path.leftContext (.none (.empty (root + 1)))).length ≤
              (BST.node left (.empty (root + 1))).height
            rw [SupportedPath.length_leftContext]
            simpa [BST.height] using length.trans (Nat.le_add_right left.height 1)
          · simp [RootPrefix.card]
      | @node _ second _ middle right =>
          obtain ⟨a, b, path, card, length, empty⟩ := ihR
          have selectedPositive : 0 < a.card := by
            have nonzero : a.card ≠ 0 := by
              intro zero
              have impossible := empty zero
              simp [BST.size] at impossible
            omega
          have finalPositive : 0 < b.card := by
            have same := path.toExecution.card_eq
            omega
          generalize equation : pullMax (BST.node middle right) = exposed at *
          cases exposed with
          | empty =>
              have := middle.lower_le_upper
              have := right.lower_le_upper
              omega
          | @node maxKey suffix =>
              cases b with
              | none => simp [RootPrefix.card] at finalPositive
              | node bLeft bRight =>
                  cases bRight with
                  | none =>
                      let last : SupportedPath
                          (.node (.none left) (.node bLeft (.none (.empty (maxKey + 1)))))
                          (.node (.node (.none left) bLeft) (.none (.empty (maxKey + 1)))) :=
                        .cons (.root (.left _ _ _)) (.rootLeft _ _ _ _ _ _) (.nil _)
                      have result : ∃ (b : RootPrefix (MaxExposed.node (BST.node left suffix)).tree)
                          (resultPath : SupportedPath (.node (.none left) a) b),
                          (RootPrefix.node (.none left) a).card ≤ (BST.node left (.node middle right)).height ∧
                          resultPath.length ≤ (BST.node left (.node middle right)).height ∧
                          ((RootPrefix.node (.none left) a).card = 0 →
                            (BST.node left (.node middle right)).size = 0) := by
                        refine ⟨_, (path.rightContext (.none left)).append last, ?_, ?_, ?_⟩
                        · simp only [RootPrefix.card, BST.height] at *
                          omega
                        · simp only [SupportedPath.length_append, SupportedPath.length_rightContext,
                            last, SupportedPath.length, BST.height] at *
                          omega
                        · simp [RootPrefix.card]
                      rw [pullMax, equation]
                      exact ⟨_, result⟩

end Splay.Accounting.OfflineNormalForm.RibStack
