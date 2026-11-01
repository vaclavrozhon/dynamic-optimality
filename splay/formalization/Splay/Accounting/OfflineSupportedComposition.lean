import Splay.Accounting.OfflineConnectedNormalization
import Splay.Accounting.OfflineSupportedPath

namespace Splay.Accounting.OfflineConnectedSupport

open Splay.Tree

namespace RootPrefix

def union {lower upper : ℕ} {tree : BST lower upper} :
    RootPrefix tree → RootPrefix tree → RootPrefix tree
  | .none _, b => b
  | .node a b, .none _ => .node a b
  | .node a b, .node c d => .node (union a c) (union b d)

theorem refines_union_left {lower upper : ℕ} {tree : BST lower upper}
    (a b : RootPrefix tree) : a.Refines (a.union b) := by
  induction a with
  | none => exact .none _
  | node left right ihL ihR =>
      cases b with
      | none => exact .refl _
      | node c d => exact .node (ihL c) (ihR d)

theorem refines_union_right {lower upper : ℕ} {tree : BST lower upper}
    (a b : RootPrefix tree) : b.Refines (a.union b) := by
  induction a with
  | none => exact .refl _
  | node left right ihL ihR =>
      cases b with
      | none => exact .none _
      | node c d => exact .node (ihL c) (ihR d)

theorem card_union_le {lower upper : ℕ} {tree : BST lower upper}
    (a b : RootPrefix tree) : (a.union b).card ≤ a.card + b.card := by
  induction a with
  | none => simp [union, card]
  | node left right ihL ihR =>
      cases b with
      | none => simp [union, card]
      | node c d =>
          have left := ihL c
          have right := ihR d
          simp only [union, card]
          omega

end RootPrefix

theorem SupportedRotationExecution.exists_path
    {lower upper length : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b) :
    ∃ path : SupportedPath a b, path.length = length := by
  induction execution with
  | refl selected => exact ⟨.nil selected, rfl⟩
  | step rotation supported tail ih =>
      obtain ⟨path, length⟩ := ih
      exact ⟨.cons rotation supported path, by simp [SupportedPath.length, length]⟩

theorem SupportedPath.exists_refine
    {lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (path : SupportedPath a b) {larger : RootPrefix before}
    (refined : a.Refines larger) :
    ∃ (last : RootPrefix after) (result : SupportedPath larger last),
      b.Refines last ∧ result.length = path.length := by
  obtain ⟨last, refines, execution⟩ := path.toExecution.refine refined
  obtain ⟨result, length⟩ := execution.exists_path
  exact ⟨last, result, refines, length⟩

/-- A finite, physically supported macro, retaining both the support charge
and the exact number of rotations as upper bounds. -/
def HasSupportedPath {lower upper : ℕ} (before after : BST lower upper)
    (support rotations : ℕ) : Prop :=
  ∃ (a : RootPrefix before) (b : RootPrefix after) (path : SupportedPath a b),
    a.card ≤ support ∧ path.length ≤ rotations

namespace HasSupportedPath

theorem refl {lower upper : ℕ} (tree : BST lower upper) :
    HasSupportedPath tree tree 0 0 := ⟨.none _, .none _, .nil _, le_rfl, le_rfl⟩

theorem mono {lower upper support rotations support' rotations' : ℕ}
    {before after : BST lower upper}
    (path : HasSupportedPath before after support rotations)
    (largerSupport : support ≤ support') (largerRotations : rotations ≤ rotations') :
    HasSupportedPath before after support' rotations' := by
  obtain ⟨a, b, path, card, cost⟩ := path
  exact ⟨a, b, path, card.trans largerSupport, cost.trans largerRotations⟩

theorem reverse {lower upper support rotations : ℕ} {before after : BST lower upper}
    (path : HasSupportedPath before after support rotations) :
    HasSupportedPath after before support rotations := by
  obtain ⟨a, b, path, card, cost⟩ := path
  have same := path.toExecution.card_eq
  exact ⟨b, a, path.reverse, by omega, by simpa using cost⟩

/-- Two macros can be charged to the union of their supports at the common
endpoint. Untouched payloads remain untouched throughout the composite. -/
theorem trans {lower upper s₁ s₂ r₁ r₂ : ℕ} {before middle after : BST lower upper}
    (first : HasSupportedPath before middle s₁ r₁)
    (second : HasSupportedPath middle after s₂ r₂) :
    HasSupportedPath before after (s₁ + s₂) (r₁ + r₂) := by
  obtain ⟨a, b, first, firstCard, firstCost⟩ := first
  obtain ⟨c, d, second, secondCard, secondCost⟩ := second
  obtain ⟨a', first', _, firstLength⟩ :=
    first.reverse.exists_refine (b.refines_union_left c)
  obtain ⟨d', second', _, secondLength⟩ :=
    second.exists_refine (b.refines_union_right c)
  have unionBound := b.card_union_le c
  have firstSame := first.toExecution.card_eq
  have refinedSame := first'.toExecution.card_eq
  refine ⟨a', d', first'.reverse.append second', by omega, ?_⟩
  simp only [SupportedPath.length_append, SupportedPath.length_reverse] at *
  omega

theorem leftContext {lower root upper support rotations : ℕ}
    {before after : BST lower root} (path : HasSupportedPath before after support rotations)
    (right : BST (root + 1) upper) :
    HasSupportedPath (.node before right) (.node after right) (support + 1) rotations := by
  obtain ⟨a, b, path, card, cost⟩ := path
  exact ⟨.node a (.none _), .node b (.none _), path.leftContext (.none _),
    by simp only [RootPrefix.card]; omega,
    by simpa using cost⟩

theorem rightContext {lower root upper support rotations : ℕ}
    {before after : BST (root + 1) upper}
    (path : HasSupportedPath before after support rotations) (left : BST lower root) :
    HasSupportedPath (.node left before) (.node left after) (support + 1) rotations := by
  obtain ⟨a, b, path, card, cost⟩ := path
  exact ⟨.node (.none _) a, .node (.none _) b, path.rightContext (.none _),
    by simp only [RootPrefix.card]; omega,
    by simpa using cost⟩

theorem rootLeft {lower x y upper : ℕ}
    (a : BST lower x) (b : BST (x + 1) y) (c : BST (y + 1) upper) :
    HasSupportedPath (.node a (.node b c)) (.node (.node a b) c) 2 1 :=
  ⟨_, _, .cons (.root (.left a b c))
    (.rootLeft a b c (.none _) (.none _) (.none _)) (.nil _), le_rfl, le_rfl⟩

theorem rootRight {lower x y upper : ℕ}
    (a : BST lower x) (b : BST (x + 1) y) (c : BST (y + 1) upper) :
    HasSupportedPath (.node (.node a b) c) (.node a (.node b c)) 2 1 :=
  (rootLeft a b c).reverse

end HasSupportedPath

end Splay.Accounting.OfflineConnectedSupport
