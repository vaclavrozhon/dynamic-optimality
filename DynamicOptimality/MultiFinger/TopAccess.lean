import ChaCha.Paper20261030.SplayAuxiliaryPotential
import MultiSplay.GlobalPreferredHoles

/-! # Splaying the retained top keys of an actual BST

The marked skeleton is a connected top tree. Each hole is the complete
physical subtree attached at that position. Splaying a retained key
changes only the skeleton, carries all those subtrees, and pays the usual
integer-rank access bound in the number of retained keys.
-/

namespace DynamicOptimality.MultiFinger.Top

open ChaCha.MTR
open Pointer (MarkedTree)
open SearchRotation
open MultiSplay.Global
open ChaCha.Paper20261030.SplayAuxiliary (potential rank splay_amortized_capacity)

variable {α : Type*}

theorem skeleton_sublist (tree : MarkedTree α) :
    tree.skeleton.inorder.Sublist tree.erase.inorder := by
  induction tree with
  | hole tree => exact List.nil_sublist _
  | node left key right ihl ihr =>
      exact (ihl.append (.refl [key])).append ihr

theorem skeleton_nodup {tree : MarkedTree α} (unique : tree.erase.inorder.Nodup) :
    tree.skeleton.inorder.Nodup := unique.sublist (skeleton_sublist tree)

theorem skeleton_root {tree : MarkedTree α} {key : α}
    (atRoot : tree.skeleton.rootKey = some key) : tree.erase.rootKey = some key := by
  cases tree with
  | hole tree => simp [MarkedTree.skeleton,Tree.rootKey] at atRoot
  | node left pivot right => exact atRoot

/-- The output is the exact ordinary splay with all original gaps retained. -/
theorem expose (before : MarkedTree α) (key : α)
    (unique : before.skeleton.inorder.Nodup) (present : key ∈ before.skeleton.inorder)
    {capacity : Nat} (fits : before.skeleton.size ≤ capacity) :
    ∃ after : MarkedTree α, ∃ rotations : Nat,
      MultiSplay.Auxiliary.Splay key before.skeleton after.skeleton rotations ∧
      after.holes = before.holes ∧ after.skeleton.rootKey = some key ∧
      after.erase.rootKey = some key ∧
      Rotations before.erase after.erase rotations ∧
      rotations+2*potential after.skeleton ≤
        2*potential before.skeleton+6*Nat.log 2 capacity+1 := by
  classical
  obtain ⟨shape,rotations,splay,_⟩ := MultiSplay.Auxiliary.exists_pointer_splay present
  let after := markedGraft shape before.gapArray 0
  have skeleton : after.skeleton = shape := markedGraft_skeleton _ _ _
  have holes : after.holes = before.holes := by
    have same := rotations_holes (splay_rotations splay) before.gapArray 0
    simpa only [after,markedGraft_gapArray] using same.symm
  have root : after.skeleton.rootKey = some key := by rw [skeleton]; exact splay.root_after
  refine ⟨after,rotations,?_,holes,root,skeleton_root root,?_,?_⟩
  · rw [skeleton]
    exact splay
  · simpa only [after,markedGraft_erase,MarkedTree.graft_gapArray] using
      rotations_graft (splay_rotations splay) before.gapArray 0
  · rw [skeleton]
    exact splay_amortized_capacity splay unique fits

end DynamicOptimality.MultiFinger.Top
