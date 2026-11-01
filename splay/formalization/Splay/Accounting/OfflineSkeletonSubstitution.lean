import Splay.Accounting.OfflineSupportedComposition
import Splay.Accounting.OfflineFrontierFolding

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree Splay.Tree.BST OfflineNormalForm

namespace SupportFrontier

def firstLeftBoundary {lower upper : ℕ} : SupportFrontier lower upper → ℕ
  | .last tree => leftBoundaryDepth tree
  | .next tree _ => leftBoundaryDepth tree

def lastRightBoundary {lower upper : ℕ} : SupportFrontier lower upper → ℕ
  | .last tree => rightBoundaryDepth tree
  | .next _ tail => tail.lastRightBoundary

@[simp] theorem firstLeftBoundary_append {lower root upper : ℕ}
    (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper) :
    (left.append right).firstLeftBoundary = left.firstLeftBoundary := by
  cases left <;> rfl

@[simp] theorem lastRightBoundary_append {lower root upper : ℕ}
    (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper) :
    (left.append right).lastRightBoundary = right.lastRightBoundary := by
  induction left with
  | last => rfl
  | next tree tail ih => exact ih right

end SupportFrontier

/-- Substitute arbitrary, ordered BST payloads for the external leaves of a
template. Template keys are ordinal placeholders; the actual keys are fixed
by the payload intervals. The witness retains the entire correspondence. -/
inductive Substitution : {templateLower templateUpper lower upper : ℕ} →
    BST templateLower templateUpper → BST lower upper → Type
  | leaf {lower upper : ℕ} (boundary : ℕ) (payload : BST lower upper) :
      Substitution (.empty boundary) payload
  | node {templateLower templateRoot templateUpper lower root upper : ℕ}
      {left : BST templateLower templateRoot} {right : BST (templateRoot + 1) templateUpper}
      {actualLeft : BST lower root} {actualRight : BST (root + 1) upper}
      (leftSubstitution : Substitution left actualLeft) (rightSubstitution : Substitution right actualRight) :
      Substitution (.node left right) (.node actualLeft actualRight)

namespace Substitution

def selected : {templateLower templateUpper lower upper : ℕ} →
    {template : BST templateLower templateUpper} → {actual : BST lower upper} →
    Substitution template actual → RootPrefix actual
  | _, _, _, _, _, _, .leaf _ payload => .none payload
  | _, _, _, _, _, _, .node left right => .node left.selected right.selected

def restrict : {templateLower templateUpper lower upper : ℕ} →
    {template : BST templateLower templateUpper} → {actual : BST lower upper} →
    Substitution template actual → RootPrefix template → RootPrefix actual
  | _, _, _, _, _, _, .leaf _ payload, .none _ => .none payload
  | _, _, _, _, _, _, .node _ _, .none _ => .none _
  | _, _, _, _, _, _, .node left right, .node a b => .node (left.restrict a) (right.restrict b)

theorem selected_card {templateLower templateUpper lower upper : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) : substitution.selected.card = template.size := by
  induction substitution with
  | leaf => rfl
  | node left right ihL ihR => simp [selected, RootPrefix.card, BST.size, ihL, ihR]

theorem restrict_card {templateLower templateUpper lower upper : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) (support : RootPrefix template) :
    (substitution.restrict support).card = support.card := by
  induction substitution with
  | leaf => cases support; rfl
  | node left right ihL ihR =>
      cases support with
      | none => rfl
      | node a b => simp [restrict, RootPrefix.card, ihL, ihR]

def AllPayloads (property : {lower upper : ℕ} → BST lower upper → Prop)
    {templateLower templateUpper lower upper : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper} :
    Substitution template actual → Prop
  | .leaf _ payload => property payload
  | .node left right => left.AllPayloads property ∧ right.AllPayloads property

theorem allPayloads_true {templateLower templateUpper lower upper : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) : substitution.AllPayloads (fun _ => True) := by
  induction substitution with
  | leaf => trivial
  | node left right ihL ihR => exact ⟨ihL, ihR⟩

theorem allPayloads_iff_frontier {property : {lower upper : ℕ} → BST lower upper → Prop}
    {templateLower templateUpper lower upper : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) :
    substitution.AllPayloads property ↔ substitution.selected.frontier.AllPayloads property := by
  induction substitution with
  | leaf => rfl
  | node left right ihL ihR =>
      simp only [AllPayloads, selected, RootPrefix.frontier, SupportFrontier.allPayloads_append, ihL, ihR]

theorem height_le {templateLower templateUpper lower upper height : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual)
    (payloads : substitution.AllPayloads (fun payload => payload.height ≤ height)) :
    actual.height ≤ template.height + height := by
  induction substitution with
  | leaf => simpa [BST.height, AllPayloads] using payloads
  | node left right ihL ihR =>
      have leftBound := ihL payloads.1
      have rightBound := ihR payloads.2
      simp only [BST.height]
      omega

theorem boundary_le {templateLower templateUpper lower upper boundary : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual)
    (payloads : substitution.AllPayloads (fun payload =>
      leftBoundaryDepth payload ≤ boundary ∧ rightBoundaryDepth payload ≤ boundary)) :
    leftBoundaryDepth actual ≤ leftBoundaryDepth template + boundary ∧
      rightBoundaryDepth actual ≤ rightBoundaryDepth template + boundary := by
  induction substitution with
  | leaf => simpa [leftBoundaryDepth, rightBoundaryDepth, AllPayloads] using payloads
  | node left right ihL ihR =>
      have leftBound := ihL payloads.1
      have rightBound := ihR payloads.2
      simp only [leftBoundaryDepth, rightBoundaryDepth]
      omega

/-- Only the two extreme payloads contribute to the two outer boundary
depths. This sharper identity prevents rib bounds from accumulating across
alternating rib replacements. -/
theorem boundary_exact {templateLower templateUpper lower upper : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) :
    leftBoundaryDepth actual = leftBoundaryDepth template + substitution.selected.frontier.firstLeftBoundary ∧
      rightBoundaryDepth actual = rightBoundaryDepth template + substitution.selected.frontier.lastRightBoundary := by
  induction substitution with
  | leaf => simp [selected, RootPrefix.frontier, SupportFrontier.firstLeftBoundary,
      SupportFrontier.lastRightBoundary, leftBoundaryDepth, rightBoundaryDepth]
  | node left right ihL ihR =>
      simp only [leftBoundaryDepth, rightBoundaryDepth, selected, RootPrefix.frontier,
        SupportFrontier.firstLeftBoundary_append, SupportFrontier.lastRightBoundary_append]
      omega

theorem ribs {templateLower templateUpper lower upper slack boundary resultSlack : ℕ}
    {template : BST templateLower templateUpper} {actual : BST lower upper}
    (substitution : Substitution template actual) (templateRibs : HasBoundedMinorRibs template slack)
    (payloadBoundary : substitution.AllPayloads (fun payload =>
      leftBoundaryDepth payload ≤ boundary ∧ rightBoundaryDepth payload ≤ boundary))
    (payloadRibs : substitution.AllPayloads (fun payload => HasBoundedMinorRibs payload resultSlack))
    (room : slack + boundary ≤ resultSlack) : HasBoundedMinorRibs actual resultSlack := by
  induction substitution with
  | leaf => exact payloadRibs
  | node left right ihL ihR =>
      have leftBound := left.boundary_le payloadBoundary.1
      have rightBound := right.boundary_le payloadBoundary.2
      exact ⟨by have := templateRibs.1; omega, by have := templateRibs.2.1; omega,
        ihL templateRibs.2.2.1 payloadBoundary.1 payloadRibs.1,
        ihR templateRibs.2.2.2 payloadBoundary.2 payloadRibs.2⟩

end Substitution

theorem SupportFrontier.exists_split {lower upper : ℕ}
    (frontier : SupportFrontier lower upper) (position : ℕ) (inside : position < frontier.card) :
    ∃ (root : ℕ) (left : SupportFrontier lower root) (right : SupportFrontier (root + 1) upper),
      frontier = left.append right ∧ left.card = position := by
  induction position generalizing lower upper with
  | zero =>
      cases frontier with
      | last => simp [SupportFrontier.card] at inside
      | next left tail => exact ⟨_, .last left, tail, rfl, rfl⟩
  | succ position ih =>
      cases frontier with
      | last => simp [SupportFrontier.card] at inside
      | next first tail =>
          obtain ⟨root, left, right, same, card⟩ := ih tail (by
            simp only [SupportFrontier.card] at inside
            omega)
          exact ⟨root, .next first left, right, by simp [SupportFrontier.append, ← same],
            by simp [SupportFrontier.card, card]⟩

/-- Every template can be filled with any ordered frontier of the right
cardinality; payload size and shape impose no further restriction. -/
theorem Substitution.exists_of_frontier {templateLower templateUpper lower upper : ℕ}
    (template : BST templateLower templateUpper) (frontier : SupportFrontier lower upper)
    (card : frontier.card = template.size) :
    ∃ (actual : BST lower upper) (substitution : Substitution template actual),
      substitution.selected.frontier = frontier := by
  induction template generalizing lower upper with
  | empty boundary =>
      cases frontier with
      | last payload => exact ⟨payload, .leaf boundary payload, rfl⟩
      | next => simp [SupportFrontier.card, BST.size] at card
  | node left right ihL ihR =>
      obtain ⟨root, leftFrontier, rightFrontier, same, leftCard⟩ := frontier.exists_split left.size (by
        simp only [BST.size] at card
        omega)
      have rightCard : rightFrontier.card = right.size := by
        rw [same, SupportFrontier.card_append] at card
        simp only [BST.size] at card
        omega
      obtain ⟨actualLeft, leftSubstitution, leftSame⟩ := ihL leftFrontier leftCard
      obtain ⟨actualRight, rightSubstitution, rightSame⟩ := ihR rightFrontier rightCard
      exact ⟨_, .node leftSubstitution rightSubstitution,
        by simp [Substitution.selected, RootPrefix.frontier, leftSame, rightSame, same]⟩

/-- A supported virtual rotation becomes one actual rotation at the same
depth. Its selected support has exactly the same cardinality. -/
theorem SupportedRotation.substitute_full
    {templateLower templateUpper lower upper depth : ℕ}
    {before after : BST templateLower templateUpper} {actualBefore : BST lower upper}
    {rotation : RotationAt depth before after} {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) (substitution : Substitution before actualBefore) :
    ∃ (actualAfter : BST lower upper) (result : Substitution after actualAfter)
      (actualRotation : RotationAt depth actualBefore actualAfter),
      SupportedRotation actualRotation (substitution.restrict a) (result.restrict b) ∧
        SupportedRotation actualRotation substitution.selected result.selected := by
  induction supported generalizing lower upper with
  | rootLeft a b c pa pb pc =>
      cases substitution with
      | node left rest =>
          cases rest with
          | node middle right =>
              exact ⟨_, .node (.node left middle) right, .root (.left _ _ _),
                .rootLeft _ _ _ _ _ _, .rootLeft _ _ _ _ _ _⟩
  | rootRight a b c pa pb pc =>
      cases substitution with
      | node rest right =>
          cases rest with
          | node left middle =>
              exact ⟨_, .node left (.node middle right), .root (.right _ _ _),
                .rootRight _ _ _ _ _ _, .rootRight _ _ _ _ _ _⟩
  | leftContext rotation supported right selectedRight ih =>
      cases substitution with
      | node left right =>
          obtain ⟨actualAfter, result, actualRotation, supported, full⟩ := ih left
          exact ⟨_, .node result right, .leftContext actualRotation _,
            .leftContext actualRotation supported _ _, .leftContext actualRotation full _ _⟩
  | rightContext left selectedLeft rotation supported ih =>
      cases substitution with
      | node left right =>
          obtain ⟨actualAfter, result, actualRotation, supported, full⟩ := ih right
          exact ⟨_, .node left result, .rightContext _ actualRotation,
            .rightContext _ _ actualRotation supported, .rightContext _ _ actualRotation full⟩

theorem SupportedRotation.substitute
    {templateLower templateUpper lower upper depth : ℕ}
    {before after : BST templateLower templateUpper} {actualBefore : BST lower upper}
    {rotation : RotationAt depth before after} {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) (substitution : Substitution before actualBefore) :
    ∃ (actualAfter : BST lower upper) (result : Substitution after actualAfter)
      (actualRotation : RotationAt depth actualBefore actualAfter),
      SupportedRotation actualRotation (substitution.restrict a) (result.restrict b) := by
  obtain ⟨after, result, rotation, supported, _⟩ := supported.substitute_full substitution
  exact ⟨after, result, rotation, supported⟩

theorem SupportedPath.substitute
    {templateLower templateUpper lower upper : ℕ}
    {before after : BST templateLower templateUpper} {actualBefore : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (path : SupportedPath a b) (substitution : Substitution before actualBefore) :
    ∃ (actualAfter : BST lower upper) (result : Substitution after actualAfter)
      (actualPath : SupportedPath (substitution.restrict a) (result.restrict b)),
      actualPath.length = path.length := by
  induction path generalizing lower upper with
  | nil selected => exact ⟨_, substitution, .nil _, rfl⟩
  | cons rotation supported tail ih =>
      obtain ⟨middle, middleSubstitution, actualRotation, supportedActual⟩ := supported.substitute substitution
      obtain ⟨actualAfter, result, actualTail, length⟩ := ih middleSubstitution
      exact ⟨actualAfter, result, .cons actualRotation supportedActual actualTail,
        by simp [SupportedPath.length, length]⟩

/-- Transfer a complete state invariant together with a path. In addition
to preserving its rotation count and every depth bound, the transfer keeps
the exact full frontier, so each payload remains literally unchanged. -/
theorem SupportedPath.substitute_checked
    {templateLower templateUpper lower upper : ℕ}
    {before after : BST templateLower templateUpper} {actualBefore : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    {payloadProperty : {lo hi : ℕ} → BST lo hi → Prop}
    {templateProperty : BST templateLower templateUpper → Prop}
    {actualProperty : BST lower upper → Prop}
    (admissible : ∀ {template : BST templateLower templateUpper} {actual : BST lower upper}
      (embedding : Substitution template actual),
      embedding.AllPayloads payloadProperty → templateProperty template → actualProperty actual)
    (path : SupportedPath a b) (substitution : Substitution before actualBefore)
    (payloads : substitution.AllPayloads payloadProperty)
    (states : path.ForallTrees templateProperty) :
    ∃ (actualAfter : BST lower upper) (result : Substitution after actualAfter)
      (actualPath : SupportedPath (substitution.restrict a) (result.restrict b)),
      result.selected.frontier = substitution.selected.frontier ∧
      actualPath.length = path.length ∧
      (∀ bound, actualPath.DepthBound bound ↔ path.DepthBound bound) ∧
      actualPath.ForallTrees actualProperty := by
  induction path generalizing actualBefore with
  | nil selected =>
      exact ⟨_, substitution, .nil _, rfl, rfl, fun _ => Iff.rfl,
        admissible substitution payloads states⟩
  | cons rotation supported tail ih =>
      obtain ⟨middle, middleSubstitution, actualRotation, supportedActual, supportedFull⟩ :=
        supported.substitute_full substitution
      have middlePayloads : middleSubstitution.AllPayloads payloadProperty := by
        rw [middleSubstitution.allPayloads_iff_frontier, ← supportedFull.frontier_eq]
        exact substitution.allPayloads_iff_frontier.mp payloads
      obtain ⟨actualAfter, result, actualTail, frontier, length, depths, geometry⟩ :=
        ih admissible middleSubstitution middlePayloads states.2
      refine ⟨actualAfter, result, .cons actualRotation supportedActual actualTail,
        frontier.trans supportedFull.frontier_eq.symm, ?_, ?_, ?_⟩
      · simp [SupportedPath.length, length]
      · intro bound
        simp only [SupportedPath.DepthBound, depths bound]
      · exact ⟨admissible substitution payloads states.1, geometry⟩

theorem HasSupportedPath.substitute
    {templateLower templateUpper lower upper support rotations : ℕ}
    {before after : BST templateLower templateUpper} {actualBefore : BST lower upper}
    (path : HasSupportedPath before after support rotations) (substitution : Substitution before actualBefore) :
    ∃ (actualAfter : BST lower upper), Nonempty (Substitution after actualAfter) ∧
      HasSupportedPath actualBefore actualAfter support rotations := by
  obtain ⟨a, b, path, card, cost⟩ := path
  obtain ⟨actualAfter, result, actualPath, length⟩ := path.substitute substitution
  exact ⟨actualAfter, ⟨result⟩, _, _, actualPath, by simpa [Substitution.restrict_card] using card, by omega⟩

theorem HasSupportedPath.substitute_exact
    {templateLower templateUpper lower upper support rotations : ℕ}
    {before after : BST templateLower templateUpper} {actualBefore : BST lower upper}
    (path : HasSupportedPath before after support rotations) (substitution : Substitution before actualBefore) :
    ∃ (actualAfter : BST lower upper) (result : Substitution after actualAfter),
      result.selected.frontier = substitution.selected.frontier ∧
      HasSupportedPath actualBefore actualAfter support rotations := by
  obtain ⟨a, b, path, card, cost⟩ := path
  obtain ⟨actualAfter, result, actualPath, frontier, length, _, _⟩ :=
    path.substitute_checked (payloadProperty := fun _ => True)
      (templateProperty := fun _ => True) (actualProperty := fun _ => True)
      (fun _ _ _ => trivial) substitution substitution.allPayloads_true
      (path.forall_height_le.imp (fun _ _ => trivial))
  exact ⟨actualAfter, result, frontier, _, _, actualPath,
    by simpa [Substitution.restrict_card] using card, by omega⟩

end Splay.Accounting.OfflineConnectedSupport
