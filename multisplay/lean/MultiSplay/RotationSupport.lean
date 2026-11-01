import MultiSplay.RawRotation
import MultiSplay.BoundedMacros

/-!
# Shallow expansion of an arbitrary comparator rotation

A rotation at depth `d` has an exact root-connected support of `d + 2`
vertices. Restricted rotations therefore reproduce its exact endpoint in at
most `4 * (d + 2)` shallow steps. The represented hanging subtrees are retained.
-/

namespace MultiSplay

open Splay.Tree (BST)
open Splay.Accounting.OfflineConnectedSupport
  (RootPrefix SupportedRotation SupportedPath exists_restrictedPath_of_sameFrontier ribs_of_height)

variable {α : Type*}

theorem Rotation.of_indexed {lower upper depth : Nat} {a b : BST lower upper}
    (rotation : BST.RotationAt depth a b) (alphabet : Nat → α) :
    Rotation depth (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw a))
      (Auxiliary.map alphabet (DynamicOptimality.BST.toRaw b)) := by
  induction rotation with
  | root step =>
      cases step with
      | right a b c => exact .right _ _ _ _ _
      | left a b c => exact .left _ _ _ _ _
  | leftContext rotation right ih => exact .leftContext ih _ _
  | rightContext left rotation ih => exact .rightContext _ _ ih

theorem rotation_support {lower upper depth : Nat} {a b : BST lower upper}
    (rotation : BST.RotationAt depth a b) :
    ∃ first : RootPrefix a, ∃ last : RootPrefix b,
      SupportedRotation rotation first last ∧ first.card = depth + 2 := by
  induction rotation with
  | root step =>
      cases step with
      | right a b c => exact ⟨_, _, .rootRight a b c (.none a) (.none b) (.none c), rfl⟩
      | left a b c => exact ⟨_, _, .rootLeft a b c (.none a) (.none b) (.none c), rfl⟩
  | leftContext rotation right ih =>
      obtain ⟨first, last, supported, card⟩ := ih
      exact ⟨_, _, .leftContext rotation supported right (.none right), by simp only [RootPrefix.card, card]⟩
  | rightContext left rotation ih =>
      obtain ⟨first, last, supported, card⟩ := ih
      exact ⟨_, _, .rightContext left (.none left) rotation supported, by simp only [RootPrefix.card, card]; omega⟩

theorem rotation_shallow {lower upper depth : Nat} {a b : BST lower upper}
    (rotation : BST.RotationAt depth a b) :
    ∃ first : RootPrefix a, ∃ last : RootPrefix b, ∃ path : SupportedPath first last,
      path.DepthBound 1 ∧ path.length ≤ 8 * (depth + 1) := by
  obtain ⟨first, last, supported, card⟩ := rotation_support rotation
  obtain ⟨path, lengthBound, shallow, _, _, _⟩ :=
    exists_restrictedPath_of_sameFrontier first last supported.frontier_eq (by omega)
      (ribs_of_height (slack := max a.height b.height) (le_max_left _ _))
      (ribs_of_height (le_max_right _ _))
  exact ⟨first, last, path, shallow, by omega⟩

end MultiSplay
