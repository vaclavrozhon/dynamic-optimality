import Splay.Accounting.OfflineSupportFrontier
import Splay.Accounting.OfflineRestrictedSpines

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree OfflineNormalForm

namespace SupportFrontier

def AllPayloads (property : {lower upper : ℕ} → BST lower upper → Prop)
    {lower upper : ℕ} : SupportFrontier lower upper → Prop
  | .last tree => property tree
  | .next left tail => property left ∧ tail.AllPayloads property

theorem allPayloads_append {property : {lower upper : ℕ} → BST lower upper → Prop}
    {lower root upper : ℕ} (left : SupportFrontier lower root)
    (right : SupportFrontier (root + 1) upper) :
    (left.append right).AllPayloads property ↔ left.AllPayloads property ∧ right.AllPayloads property := by
  induction left with
  | last => rfl
  | next tree tail ih => simp only [append, AllPayloads, ih, and_assoc]

theorem exists_last {lower upper : ℕ} (frontier : SupportFrontier lower upper)
    (positive : 0 < frontier.card) :
    ∃ (root : ℕ) (initial : SupportFrontier lower root) (right : BST (root + 1) upper),
      frontier = initial.append (.last right) := by
  induction frontier with
  | last => simp [card] at positive
  | next left tail ih =>
      cases tail with
      | last right => exact ⟨_, .last left, right, rfl⟩
      | next middle rest =>
          obtain ⟨root, initial, right, equal⟩ := ih (by simp [card])
          exact ⟨root, .next left initial, right, by rw [append, ← equal]⟩

end SupportFrontier

namespace FrontierFolding

/-- Length of the initial run in the specified direction. False follows
right children (taking smallest keys); true follows left children. -/
def initialRun (direction : Bool) : List Bool → ℕ
  | [] => 0
  | first :: tail => if first = direction then initialRun direction tail + 1 else 0

def BoundedRuns (bound : ℕ) : List Bool → Prop
  | [] => True
  | first :: tail => initialRun first (first :: tail) ≤ bound ∧ BoundedRuns bound tail

theorem BoundedRuns.initial_le {bound : ℕ} {word : List Bool}
    (bounded : BoundedRuns bound word) (direction : Bool) : initialRun direction word ≤ bound := by
  cases word with
  | nil => simp [initialRun]
  | cons first tail =>
      by_cases equal : first = direction
      · subst direction
        exact bounded.1
      · simp [initialRun, equal]

def PayloadGeometry {lower upper : ℕ} (tree : BST lower upper) : Prop :=
  HasBoundedMinorRibs tree 4 ∧ leftBoundaryDepth tree ≤ 2 ∧ rightBoundaryDepth tree ≤ 2

/-- A folding retains the entire inorder frontier. Every chosen key is
taken from one end, so all selected nodes lie on one turning spine. -/
inductive Fold : {lower upper : ℕ} → List Bool → SupportFrontier lower upper → BST lower upper → Prop
  | last {lower upper : ℕ} (tree : BST lower upper) : Fold [] (.last tree) tree
  | low {lower root upper : ℕ} {word : List Bool}
      (left : BST lower root) {tail : SupportFrontier (root + 1) upper}
      {tree : BST (root + 1) upper} (folded : Fold word tail tree) :
      Fold (false :: word) (.next left tail) (.node left tree)
  | high {lower root upper : ℕ} {word : List Bool}
      {initial : SupportFrontier lower root} {tree : BST lower root}
      (folded : Fold word initial tree) (right : BST (root + 1) upper) :
      Fold (true :: word) (initial.append (.last right)) (.node tree right)

theorem exists_fold {lower upper : ℕ} (frontier : SupportFrontier lower upper)
    (word : List Bool) (length : word.length = frontier.card) :
    ∃ tree : BST lower upper, Fold word frontier tree := by
  induction word generalizing lower upper with
  | nil =>
      cases frontier with
      | last tree => exact ⟨tree, .last tree⟩
      | next => simp [SupportFrontier.card] at length
  | cons direction word ih =>
      cases direction with
      | false =>
          cases frontier with
          | last => simp [SupportFrontier.card] at length
          | next left tail =>
              obtain ⟨tree, folded⟩ := ih tail (by simpa [SupportFrontier.card] using length)
              exact ⟨.node left tree, .low left folded⟩
      | true =>
          obtain ⟨root, initial, right, equal⟩ := frontier.exists_last (by
            simp only [List.length_cons] at length
            omega)
          subst frontier
          obtain ⟨tree, folded⟩ := ih initial (by simpa [SupportFrontier.card] using length)
          exact ⟨.node tree right, .high folded right⟩

theorem Fold.root_low {lower root upper : ℕ} {word : List Bool}
    {left : BST lower root} {tail : SupportFrontier (root + 1) upper} {tree : BST lower upper}
    (folded : Fold (false :: word) (.next left tail) tree) : tree.HasRoot root := by
  cases folded
  exact ⟨_, _, rfl⟩

theorem Fold.exists_selected {lower upper : ℕ} {word : List Bool}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper}
    (folded : Fold word frontier tree) :
    ∃ selected : RootPrefix tree, selected.frontier = frontier ∧ selected.card = word.length := by
  induction folded with
  | last tree => exact ⟨.none tree, rfl, rfl⟩
  | low left folded ih =>
      obtain ⟨selected, same, card⟩ := ih
      exact ⟨.node (.none left) selected,
        by simp [RootPrefix.frontier, SupportFrontier.append, same],
        by simp [RootPrefix.card, card, Nat.add_comm]⟩
  | high folded right ih =>
      obtain ⟨selected, same, card⟩ := ih
      exact ⟨.node selected (.none right),
        by simp [RootPrefix.frontier, same], by simp [RootPrefix.card, card]⟩

theorem Fold.geometry {lower upper : ℕ} {word : List Bool}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper}
    (folded : Fold word frontier tree) (payloads : frontier.AllPayloads PayloadGeometry)
    (bounded : BoundedRuns 3 word) :
    HasBoundedMinorRibs tree 7 ∧
      leftBoundaryDepth tree ≤ initialRun true word + 3 ∧
      rightBoundaryDepth tree ≤ initialRun false word + 3 := by
  induction folded with
  | last tree =>
      exact ⟨payloads.1.mono (by decide), by simpa [initialRun] using payloads.2.1.trans (by decide),
        by simpa [initialRun] using payloads.2.2.trans (by decide)⟩
  | low left folded ih =>
      obtain ⟨ribs, leftBound, rightBound⟩ := ih payloads.2 bounded.2
      have tailRun := bounded.2.initial_le true
      refine ⟨⟨by have := payloads.1.2.2; omega, by omega,
        payloads.1.1.mono (by decide), ribs⟩, ?_, ?_⟩
      · have := payloads.1.2.1
        simp only [initialRun, Bool.false_eq_true, if_false, leftBoundaryDepth]
        omega
      · simp only [initialRun, if_true, rightBoundaryDepth]
        omega
  | high folded right ih =>
      obtain ⟨initialPayloads, rightPayload⟩ := (SupportFrontier.allPayloads_append _ _).mp payloads
      obtain ⟨ribs, leftBound, rightBound⟩ := ih initialPayloads bounded.2
      have tailRun := bounded.2.initial_le false
      refine ⟨⟨by omega, by have := rightPayload.2.1; omega,
        ribs, rightPayload.1.mono (by decide)⟩, ?_, ?_⟩
      · simp only [initialRun, if_true, leftBoundaryDepth]
        omega
      · have := rightPayload.2.2
        simp only [initialRun, Bool.true_eq_false, if_false, rightBoundaryDepth]
        omega

theorem Fold.height_le {lower upper height : ℕ} {word : List Bool}
    {frontier : SupportFrontier lower upper} {tree : BST lower upper}
    (folded : Fold word frontier tree)
    (payloads : frontier.AllPayloads (fun payload => payload.height ≤ height)) :
    tree.height ≤ word.length + height := by
  induction folded with
  | last => simpa [SupportFrontier.AllPayloads] using payloads
  | low left folded ih =>
      have rest := ih payloads.2
      have first := payloads.1
      simp only [BST.height, List.length_cons]
      omega
  | high folded right ih =>
      obtain ⟨initialPayloads, rightPayload⟩ := (SupportFrontier.allPayloads_append _ _).mp payloads
      have rest := ih initialPayloads
      have lastBound : right.height ≤ height := rightPayload
      simp only [BST.height, List.length_cons]
      omega

end FrontierFolding

end Splay.Accounting.OfflineConnectedSupport
