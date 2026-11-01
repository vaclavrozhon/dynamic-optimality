import MultiSplay.AuxiliarySplay
import DynamicOptimality.SearchRotationModel

/-!
# Exact ordinary rotations of an auxiliary splay

An auxiliary tree is a skeleton in one actual BST. Its inorder gaps hold
opaque foreign subtrees, and an ordinary zipper describes its location
inside the whole tree. Every standard auxiliary rotation remains exactly
one ordinary rotation after those subtrees and ancestors are restored.
No navigation cost or component-boundary crossing is introduced.
-/

namespace MultiSplay.Global

open DynamicOptimality DynamicOptimality.SearchRotation
open TangoSquared.MTR
open TangoSquared.MTR.Tree (graft size)

variable {α : Type*}

theorem rotation_size {before after : RawTree α} (step : Rotation before after) :
    before.size = after.size := by
  induction step <;> simp_all [Tree.size] <;> omega

/-- Inorder-numbered foreign subtrees retain their exact identities. -/
theorem rotation_graft {before after : RawTree α} (step : Rotation before after)
    (gaps : Nat → RawTree α) (start : Nat) :
    Rotation (graft before gaps start) (graft after gaps start) := by
  induction step generalizing start with
  | rootRight a b c x y =>
    simp only [graft, size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    exact .rootRight _ _ _ _ _
  | rootLeft a b c x y =>
    simp only [graft, size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    exact .rootLeft _ _ _ _ _
  | leftContext step key right ih =>
    simp only [graft, rotation_size step]
    exact .leftContext (ih start) key _
  | rightContext left key step ih =>
    exact .rightContext _ key (ih _)

theorem rotations_graft {before after : RawTree α} {count : Nat}
    (trace : Rotations before after count) (gaps : Nat → RawTree α) (start : Nat) :
    Rotations (graft before gaps start) (graft after gaps start) count := by
  induction trace with
  | refl tree => exact .refl _
  | step head tail ih => exact .step (rotation_graft head gaps start) ih

/-- These are the standard zig-zig and zig-zag rotations in their original
order, including when the double rotation occurs below the auxiliary root. -/
theorem double_rotations {key : α} {before after : RawTree α}
    (step : Auxiliary.Double key before after) : Rotations before after 2 := by
  induction step with
  | leftLeft a b c d y z =>
    exact .step (.rootRight (.node a _ b) c d y z)
      (.singleton (.rootRight a b (.node c z d) _ y))
  | rightRight a b c d x y =>
    exact .step (.rootLeft a b (.node c _ d) x y)
      (.singleton (.rootLeft (.node a x b) c d y _))
  | leftRight a b c d x z =>
    exact .step (.leftContext (.rootLeft a b c x _) z d)
      (.singleton (.rootRight (.node a x b) c d _ z))
  | rightLeft a b c d x z =>
    exact .step (.rightContext a x (.rootRight b c d _ z))
      (.singleton (.rootLeft a b (.node c z d) x _))
  | leftContext step x r ih =>
    exact ih.plug [.left x r]
  | rightContext l x step ih =>
    exact ih.plug [.right l x]

theorem step_rotations {key : α} {before after : RawTree α} {count : Nat}
    (step : Auxiliary.Step key before after count) : Rotations before after count := by
  cases step with
  | zigLeft a b c y => exact .singleton (.rootRight a b c _ y)
  | zigRight a b c x => exact .singleton (.rootLeft a b c x _)
  | double step => exact double_rotations step

/-- A full auxiliary splay has exactly its specified ordinary-rotation count. -/
theorem splay_rotations {key : α} {before after : RawTree α} {count : Nat}
    (splay : Auxiliary.Splay key before after count) : Rotations before after count := by
  induction splay with
  | done => exact .refl _
  | next step rest ih => exact (step_rotations step).append ih

/-- The complete physical lift preserves all hanging trees and the outer
context; it uses the exact auxiliary splay, without extra rotations. -/
theorem splay_embedded {key : α} {before after : RawTree α} {count : Nat}
    (splay : Auxiliary.Splay key before after count)
    (gaps : Nat → RawTree α) (start : Nat) (ancestors : List (Pointer.Frame α)) :
    Rotations (Pointer.plug (graft before gaps start) ancestors)
      (Pointer.plug (graft after gaps start) ancestors) count :=
  (rotations_graft (splay_rotations splay) gaps start).plug ancestors

/-- A marked connected component already supplies its exact opaque gap
array. Only its skeleton is splayed; its actual hanging trees are retained. -/
theorem splay_marked {key : α} (before : Pointer.MarkedTree α)
    {after : RawTree α} {count : Nat}
    (splay : Auxiliary.Splay key before.skeleton after count)
    (ancestors : List (Pointer.Frame α)) :
    Rotations (Pointer.plug before.erase ancestors)
      (Pointer.plug (graft after before.gapArray 0) ancestors) count := by
  have lifted := splay_embedded splay before.gapArray 0 ancestors
  rw [before.graft_gapArray] at lifted
  exact lifted

end MultiSplay.Global
