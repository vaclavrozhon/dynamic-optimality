import Splay.Accounting.OfflineConnectedNormalization
import Splay.Accounting.OfflineStructuralRibBridge

/-!
# A uniform rib invariant for the restricted-rotation conversion

The two outer spines are allowed to grow. Every subtree hanging off them has
bounded inward ribs and bounded left and right boundary paths. Root rotations
preserve this invariant. Promoting the right child of the left child merely
splits one such hanging subtree into two smaller ones.

This gives one additional unit of rib slack for the entire conversion,
independently of the number of rotations.
-/

namespace Splay.Accounting.OfflineNormalForm

open Splay.Tree

theorem HasBoundedMinorRibs.mono {lower upper small large : ℕ}
    {tree : BST lower upper} (ribs : HasBoundedMinorRibs tree small)
    (bound : small ≤ large) : HasBoundedMinorRibs tree large := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      exact ⟨ribs.1.trans bound, ribs.2.1.trans bound,
        ihL ribs.2.2.1, ihR ribs.2.2.2⟩

namespace RestrictedSpines

/-- A subtree outside both outer spines. -/
def InteriorSafe {lower upper : ℕ} (tree : BST lower upper) (slack : ℕ) : Prop :=
  HasBoundedMinorRibs tree slack ∧
    leftBoundaryDepth tree < slack ∧ rightBoundaryDepth tree < slack

def LeftSafe : {lower upper : ℕ} → BST lower upper → ℕ → Prop
  | _, _, .empty _, _ => True
  | _, _, .node left right, slack => LeftSafe left slack ∧ InteriorSafe right slack

def RightSafe : {lower upper : ℕ} → BST lower upper → ℕ → Prop
  | _, _, .empty _, _ => True
  | _, _, .node left right, slack => InteriorSafe left slack ∧ RightSafe right slack

def SpineSafe : {lower upper : ℕ} → BST lower upper → ℕ → Prop
  | _, _, .empty _, _ => True
  | _, _, .node left right, slack => LeftSafe left slack ∧ RightSafe right slack

theorem InteriorSafe.left {lower root upper slack : ℕ}
    {left : BST lower root} {right : BST (root + 1) upper}
    (safe : InteriorSafe (.node left right) slack) : InteriorSafe left slack := by
  rcases safe with ⟨⟨leftAtRoot, rightAtRoot, leftRibs, rightRibs⟩, leftBound, rightBound⟩
  refine ⟨leftRibs, ?_, ?_⟩
  · simp only [leftBoundaryDepth] at leftBound
    omega
  · omega

theorem InteriorSafe.right {lower root upper slack : ℕ}
    {left : BST lower root} {right : BST (root + 1) upper}
    (safe : InteriorSafe (.node left right) slack) : InteriorSafe right slack := by
  rcases safe with ⟨⟨leftAtRoot, rightAtRoot, leftRibs, rightRibs⟩, leftBound, rightBound⟩
  refine ⟨rightRibs, ?_, ?_⟩
  · omega
  · simp only [rightBoundaryDepth] at rightBound
    omega

theorem leftSafe_of_ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (ribs : HasBoundedMinorRibs tree slack) (boundary : rightBoundaryDepth tree < slack) :
    LeftSafe tree slack := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      refine ⟨ihL ribs.2.2.1 (by have := ribs.1; omega), ribs.2.2.2, ?_, ?_⟩
      · have := ribs.2.1
        omega
      · simp only [rightBoundaryDepth] at boundary
        omega

theorem rightSafe_of_ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (ribs : HasBoundedMinorRibs tree slack) (boundary : leftBoundaryDepth tree < slack) :
    RightSafe tree slack := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      refine ⟨⟨ribs.2.2.1, ?_, ?_⟩, ihR ribs.2.2.2 (by have := ribs.2.1; omega)⟩
      · simp only [leftBoundaryDepth] at boundary
        omega
      · have := ribs.1
        omega

theorem spineSafe_of_ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (ribs : HasBoundedMinorRibs tree slack) : SpineSafe tree slack := by
  cases tree with
  | empty => trivial
  | node left right =>
      exact ⟨leftSafe_of_ribs ribs.2.2.1 (by have := ribs.1; omega),
        rightSafe_of_ribs ribs.2.2.2 (by have := ribs.2.1; omega)⟩

theorem LeftSafe.boundary_le {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : LeftSafe tree slack) : rightBoundaryDepth tree ≤ slack := by
  cases tree with
  | empty => exact Nat.zero_le _
  | node left right =>
      have := safe.2.2.2
      simp only [rightBoundaryDepth]
      omega

theorem RightSafe.boundary_le {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : RightSafe tree slack) : leftBoundaryDepth tree ≤ slack := by
  cases tree with
  | empty => exact Nat.zero_le _
  | node left right =>
      have := safe.1.2.1
      simp only [leftBoundaryDepth]
      omega

theorem LeftSafe.ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : LeftSafe tree slack) : HasBoundedMinorRibs tree (slack + 1) := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      have leftBound := safe.1.boundary_le
      have rightBound := safe.2.2.1
      exact ⟨by omega, by omega, ihL safe.1, safe.2.1.mono (by omega)⟩

theorem RightSafe.ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : RightSafe tree slack) : HasBoundedMinorRibs tree (slack + 1) := by
  induction tree with
  | empty => trivial
  | node left right ihL ihR =>
      have leftBound := safe.1.2.2
      have rightBound := safe.2.boundary_le
      exact ⟨by omega, by omega, safe.1.1.mono (by omega), ihR safe.2⟩

theorem SpineSafe.ribs {lower upper slack : ℕ} {tree : BST lower upper}
    (safe : SpineSafe tree slack) : HasBoundedMinorRibs tree (slack + 1) := by
  cases tree with
  | empty => trivial
  | node left right =>
      have leftBound := safe.1.boundary_le
      have rightBound := safe.2.boundary_le
      exact ⟨by omega, by omega, safe.1.ribs, safe.2.ribs⟩

/-- Arbitrarily many root rotations preserve the same spine invariant. -/
theorem SpineSafe.rootRotate {lower upper slack : ℕ} {before after : BST lower upper}
    (safe : SpineSafe before slack) (rotation : BST.RootRotation before after) :
    SpineSafe after slack := by
  cases rotation with
  | right a b c => exact ⟨safe.1.1, safe.1.2, safe.2⟩
  | left a b c => exact ⟨⟨safe.1, safe.2.1⟩, safe.2.2⟩

/-- The other move in the conversion exposes part of an interior subtree. -/
theorem SpineSafe.leftChildLeft {lower first second root upper slack : ℕ}
    {a : BST lower first} {b : BST (first + 1) second}
    {c : BST (second + 1) root} {d : BST (root + 1) upper}
    (safe : SpineSafe (.node (.node a (.node b c)) d) slack) :
    SpineSafe (.node (.node (.node a b) c) d) slack :=
  ⟨⟨⟨safe.1.1, safe.1.2.left⟩, safe.1.2.right⟩, safe.2⟩

end RestrictedSpines
end Splay.Accounting.OfflineNormalForm

namespace Splay.Accounting.OfflineConnectedSupport

namespace RootPrefix

/-- Maximum height of an untouched hanging subtree. -/
def frontierHeight {lower upper : ℕ} {tree : BST lower upper} : RootPrefix tree → ℕ
  | .none tree => tree.height
  | .node left right => max left.frontierHeight right.frontierHeight

theorem frontierHeight_le_height {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) : selected.frontierHeight ≤ tree.height := by
  induction selected with
  | none => exact le_rfl
  | node left right ihL ihR =>
      simp only [frontierHeight, Splay.Tree.BST.height]
      omega

theorem height_le_card_add_frontierHeight {lower upper : ℕ} {tree : BST lower upper}
    (selected : RootPrefix tree) : tree.height ≤ selected.card + selected.frontierHeight := by
  induction selected with
  | none => simp [card, frontierHeight]
  | node left right ihL ihR =>
      simp only [card, frontierHeight, Splay.Tree.BST.height] at *
      omega

end RootPrefix

theorem SupportedRotation.frontierHeight_eq
    {depth lower upper : ℕ} {before after : BST lower upper}
    {rotation : Splay.Tree.BST.RotationAt depth before after}
    {a : RootPrefix before} {b : RootPrefix after}
    (supported : SupportedRotation rotation a b) : a.frontierHeight = b.frontierHeight := by
  induction supported with
  | rootRight => simp [RootPrefix.frontierHeight, max_assoc]
  | rootLeft => simp [RootPrefix.frontierHeight, max_assoc]
  | leftContext rotation supported right rightPrefix ih =>
      simp [RootPrefix.frontierHeight, ih]
  | rightContext left leftPrefix rotation supported ih =>
      simp [RootPrefix.frontierHeight, ih]

theorem SupportedRotationExecution.frontierHeight_eq
    {length lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b) : a.frontierHeight = b.frontierHeight := by
  induction execution with
  | refl => rfl
  | step rotation supported tail ih => exact supported.frontierHeight_eq.trans ih

/-- A supported execution can increase height only through the selected nodes,
independently of its rotation count. This also applies to every prefix of it. -/
theorem SupportedRotationExecution.height_le
    {length lower upper : ℕ} {before after : BST lower upper}
    {a : RootPrefix before} {b : RootPrefix after}
    (execution : SupportedRotationExecution length a b) : after.height ≤ before.height + a.card := by
  have finalBound := b.height_le_card_add_frontierHeight
  have sameCard := execution.card_eq
  have sameFrontier := execution.frontierHeight_eq
  have initialBound := a.frontierHeight_le_height
  omega

end Splay.Accounting.OfflineConnectedSupport
