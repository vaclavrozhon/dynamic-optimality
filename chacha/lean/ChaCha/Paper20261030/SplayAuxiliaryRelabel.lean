import DynamicOptimality.PointerRelabel
import DynamicOptimality.SearchRotationModel

/-! The dyadic accounting uses integer labels. Relabeling its nonnegative
physical keys by `Int.toNat` preserves every search depth and every actual
rotation, so the public strategy uses the shared natural-key interface. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality DynamicOptimality.SearchRotation MTR.Tree

 theorem relabel_rotation {α β : Type*} (f : α → β) {before after : RawTree α}
    (step : Rotation before after) : Rotation (Relabel.tree f before) (Relabel.tree f after) := by
  induction step with
  | rootRight a b c x y => exact .rootRight _ _ _ _ _
  | rootLeft a b c x y => exact .rootLeft _ _ _ _ _
  | leftContext step key right ih => exact .leftContext ih _ _
  | rightContext left key step ih => exact .rightContext _ _ ih

 theorem relabel_rotations {α β : Type*} (f : α → β) {before after : RawTree α} {count : Nat}
    (trace : Rotations before after count) : Rotations (Relabel.tree f before) (Relabel.tree f after) count := by
  induction trace with
  | refl => exact .refl _
  | step first rest ih => exact .step (relabel_rotation f first) ih

 theorem searchDepth_toNat (tree : RawTree Int) (key : Int) (nonnegative : 0 ≤ key)
    (keys : ∀ value ∈ tree.inorder, 0 ≤ value) :
    searchDepth key.toNat (Relabel.tree Int.toNat tree) = searchDepth key tree := by
  induction tree with
  | empty => rfl
  | node left root right ihl ihr =>
    have rootNonnegative : 0 ≤ root := keys root (by simp [inorder])
    have leftKeys : ∀ value ∈ left.inorder, 0 ≤ value := fun value member => keys value (by simp [inorder,member])
    have rightKeys : ∀ value ∈ right.inorder, 0 ≤ value := fun value member => keys value (by simp [inorder,member])
    have compareLeft : key.toNat < root.toNat ↔ key < root := by
      omega
    have compareRight : root.toNat < key.toNat ↔ root < key := by
      omega
    simp only [Relabel.tree,searchDepth,compareLeft,compareRight,ihl leftKeys,ihr rightKeys]

 theorem access_toNat {before after : RawTree Int} {key : Int} {cost : Nat}
    (nonnegative : 0 ≤ key) (keys : ∀ value ∈ before.inorder, 0 ≤ value)
    (access : Access key before after cost) :
    Access key.toNat (Relabel.tree Int.toNat before) (Relabel.tree Int.toNat after) cost := by
  obtain ⟨depth,count,searched,trace,paid⟩ := access
  exact ⟨depth,count,(searchDepth_toNat before key nonnegative keys).trans searched,relabel_rotations _ trace,paid⟩

end ChaCha.Paper20261030.SplayAuxiliary
