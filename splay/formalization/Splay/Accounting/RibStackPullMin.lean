import Splay.Accounting.OfflineSupportedPath

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Splay.Tree
open OfflineConnectedSupport RestrictedSpines

/-- A tree with its minimum key exposed and an empty left child. -/
inductive MinExposed : ℕ → ℕ → Type
  | empty (boundary : ℕ) : MinExposed boundary boundary
  | node {root upper : ℕ} (right : BST (root + 1) upper) : MinExposed root upper

namespace MinExposed

def tree : {lower upper : ℕ} → MinExposed lower upper → BST lower upper
  | _, _, .empty boundary => BST.empty boundary
  | _, _, .node right => BST.node (BST.empty _) right

def inwardDepth {lower upper : ℕ} : MinExposed lower upper → ℕ
  | .empty _ => 0
  | .node right => leftBoundaryDepth right

theorem leftBoundary_le_one {lower upper : ℕ} (exposed : MinExposed lower upper) :
    leftBoundaryDepth exposed.tree ≤ 1 := by
  cases exposed <;> simp [tree, leftBoundaryDepth]

def joinRoot {lower root upper : ℕ} (exposed : MinExposed lower root)
    (right : BST (root + 1) upper) (rightExposed : MinExposed (root + 1) upper) :
    MinExposed lower upper :=
  match exposed with
  | .empty _ => .node rightExposed.tree
  | .node leftRight => .node (BST.node leftRight right)

end MinExposed

/-- The symmetric successor-pulling operation. -/
def pullMin {lower upper : ℕ} : BST lower upper → MinExposed lower upper
  | .empty boundary => .empty boundary
  | .node left right => MinExposed.joinRoot (pullMin left) right (pullMin right)

theorem pullMin_empty (boundary : ℕ) : pullMin (BST.empty boundary) = .empty boundary := rfl

theorem pullMin_node {lower root upper : ℕ}
    (left : BST lower root) (right : BST (root + 1) upper) :
    pullMin (BST.node left right) = MinExposed.joinRoot (pullMin left) right (pullMin right) := rfl

theorem pullMin_height_le {lower upper : ℕ} (tree : BST lower upper) :
    (pullMin tree).tree.height ≤ tree.height + 1 := by
  induction tree with
  | empty => simp [pullMin_empty, MinExposed.tree, BST.height]
  | node left right ihL ihR =>
      generalize equation : pullMin left = exposed at *
      cases exposed with
      | empty =>
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.tree, BST.height] at *
          omega
      | node leftRight =>
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.tree, BST.height] at *
          omega

theorem pullMin_rightBoundary_le {lower upper : ℕ} (tree : BST lower upper) :
    rightBoundaryDepth (pullMin tree).tree ≤ rightBoundaryDepth tree + 1 := by
  induction tree with
  | empty => simp [pullMin_empty, MinExposed.tree, rightBoundaryDepth]
  | node left right ihL ihR =>
      generalize equation : pullMin left = exposed at *
      cases exposed with
      | empty =>
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.tree, rightBoundaryDepth] at *
          omega
      | node leftRight => simp [pullMin_node, MinExposed.joinRoot, equation, MinExposed.tree, rightBoundaryDepth]

theorem pullMin_inwardDepth_le {lower upper : ℕ} (tree : BST lower upper) :
    (pullMin tree).inwardDepth ≤ leftBoundaryDepth tree := by
  induction tree with
  | empty => simp [pullMin_empty, MinExposed.inwardDepth, leftBoundaryDepth]
  | node left right ihL ihR =>
      generalize equation : pullMin left = exposed at *
      cases exposed with
      | empty =>
          have bound := (pullMin right).leftBoundary_le_one
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.inwardDepth, leftBoundaryDepth]
          omega
      | node leftRight =>
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.inwardDepth, leftBoundaryDepth] at *
          omega

theorem pullMin_ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : InteriorSafe tree slack) : HasBoundedMinorRibs (pullMin tree).tree slack := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      have leftSafe := safe.left
      have rightSafe := safe.right
      have leftRibs := ihL leftSafe
      have rightRibs := ihR rightSafe
      have boundary := pullMin_rightBoundary_le left
      have inward := pullMin_inwardDepth_le (BST.node left right)
      have positive : 0 < slack := by have := safe.2.1; omega
      generalize equation : pullMin left = exposed at *
      cases exposed with
      | empty =>
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.tree, MinExposed.inwardDepth] at inward ⊢
          refine ⟨by change 1 ≤ slack; omega,
            Nat.succ_le_of_lt (lt_of_le_of_lt inward safe.2.1), trivial, rightRibs⟩
      | node leftRight =>
          simp only [pullMin_node, MinExposed.joinRoot, equation, MinExposed.tree, MinExposed.inwardDepth] at *
          refine ⟨by change 1 ≤ slack; omega, ?_, trivial, ?_⟩
          · have := safe.2.1
            omega
          · refine ⟨?_, safe.1.2.1, leftRibs.2.2.2, rightSafe.1⟩
            have original := safe.1.1
            simp only [rightBoundaryDepth] at boundary
            omega

theorem exists_pullMin_path {lower upper : ℕ} (tree : BST lower upper) :
    ∃ (a : RootPrefix tree) (b : RootPrefix (pullMin tree).tree) (path : SupportedPath a b),
      a.card ≤ tree.height ∧ path.length ≤ tree.height ∧
        (a.card = 0 → tree.size = 0) := by
  induction tree with
  | empty boundary => exact ⟨.none _, .none _, .nil _, le_rfl, le_rfl, fun _ => rfl⟩
  | @node lower root upper left right ihL ihR =>
      cases left with
      | empty =>
          obtain ⟨a, b, path, card, length, empty⟩ := ihR
          refine ⟨.node (.none _) a, .node (.none _) b, path.rightContext (.none _), ?_, ?_, ?_⟩
          · simp only [RootPrefix.card, BST.height]
            omega
          · change (path.rightContext (.none (.empty lower))).length ≤
              (BST.node (.empty lower) right).height
            rw [SupportedPath.length_rightContext]
            simpa [BST.height] using length.trans (Nat.le_add_right right.height 1)
          · simp [RootPrefix.card]
      | @node lower first _ left middle =>
          obtain ⟨a, b, path, card, length, empty⟩ := ihL
          have selectedPositive : 0 < a.card := by
            have nonzero : a.card ≠ 0 := by
              intro zero
              have impossible := empty zero
              simp [BST.size] at impossible
            omega
          have finalPositive : 0 < b.card := by
            have same := path.toExecution.card_eq
            omega
          generalize equation : pullMin (BST.node left middle) = exposed at *
          cases exposed with
          | empty =>
              have := left.lower_le_upper
              have := middle.lower_le_upper
              omega
          | node suffix =>
              cases b with
              | none => simp [RootPrefix.card] at finalPositive
              | node bLeft bRight =>
                  cases bLeft with
                  | none =>
                      let last : SupportedPath
                          (.node (.node (.none (.empty lower)) bRight) (.none right))
                          (.node (.none (.empty lower)) (.node bRight (.none right))) :=
                        .cons (.root (.right _ _ _)) (.rootRight _ _ _ _ _ _) (.nil _)
                      have result : ∃ (b : RootPrefix (MinExposed.node (BST.node suffix right)).tree)
                          (resultPath : SupportedPath (.node a (.none right)) b),
                          (RootPrefix.node a (.none right)).card ≤ (BST.node (.node left middle) right).height ∧
                          resultPath.length ≤ (BST.node (.node left middle) right).height ∧
                          ((RootPrefix.node a (.none right)).card = 0 →
                            (BST.node (.node left middle) right).size = 0) := by
                        refine ⟨_, (path.leftContext (.none right)).append last, ?_, ?_, ?_⟩
                        · simp only [RootPrefix.card, BST.height] at *
                          omega
                        · simp only [SupportedPath.length_append, SupportedPath.length_leftContext,
                            last, SupportedPath.length, BST.height] at *
                          omega
                        · simp [RootPrefix.card]
                      rw [pullMin_node, equation]
                      exact ⟨_, result⟩

end Splay.Accounting.OfflineNormalForm.RibStack
