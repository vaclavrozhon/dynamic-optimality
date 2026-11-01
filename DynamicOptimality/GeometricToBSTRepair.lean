import DynamicOptimality.GeometricToBSTMarked
import DynamicOptimality.GeometricRowBounds

/-!
# Repairing one geometric row backwards

A satisfying row meets a maximum of the old height in every interval it
meets. Repeatedly choose such a marked maximum as the root and recurse.
The resulting tree is an old-height heap, and every unmarked hanging
subtree is retained verbatim in its original inorder gap.
-/

namespace DynamicOptimality.Geometry

open TangoSquared TangoSquared.MTR TangoSquared.MTR.Tree
open TangoSquared.MTR.Pointer TangoSquared.MTR.Tree.PriorityHull
open GreedyMerge.Geometry

theorem repair_marked {n lo hi : Nat} {height : Nat → Int} {row : Finset Nat}
    (satisfied : RowSatisfies height n row) (upper : hi ≤ n)
    (marked : MarkedTree Nat) (ordered : Ordered marked.erase)
    (keys : ∀ key, key ∈ marked.erase.inorder ↔ lo ≤ key ∧ key < hi)
    (selected : ∀ key ∈ marked.erase.inorder,
      key ∈ marked.skeleton.inorder ↔ key ∈ row)
    (holesHeap : ∀ tree ∈ marked.holes, Heap height tree) :
    ∃ repaired : MarkedTree Nat,
      repaired.skeleton.inorder = marked.skeleton.inorder ∧
      repaired.holes = marked.holes ∧
      repaired.erase.inorder = marked.erase.inorder ∧ Heap height repaired.erase := by
  generalize sizeEq : marked.skeleton.size = count
  induction count using Nat.strong_induction_on generalizing marked lo hi with
  | h count ih =>
    cases marked with
    | hole tree =>
        exact ⟨.hole tree, rfl, rfl, rfl, holesHeap tree (by simp [MarkedTree.holes])⟩
    | node oldLeft oldRoot oldRight =>
        let marked := MarkedTree.node oldLeft oldRoot oldRight
        have oldMember : oldRoot ∈ marked.erase.inorder := by simp [marked, MarkedTree.erase, inorder]
        have oldSelected : oldRoot ∈ row :=
          (selected oldRoot oldMember).mp (by simp [MarkedTree.skeleton, inorder])
        have oldBounds := (keys oldRoot).mp oldMember
        obtain ⟨root, rootSelected, rootLo, rootHi, maximal⟩ :=
          interval_has_selected_max satisfied upper ⟨oldRoot, oldSelected, oldBounds⟩
        have rootMember : root ∈ marked.skeleton.inorder :=
          (selected root ((keys root).mpr ⟨rootLo, rootHi⟩)).mpr rootSelected
        obtain ⟨left, right, movedEq⟩ := Marked.moveToRoot_node marked root ordered rootMember
        have movedInorder : (MarkedTree.node left root right).erase.inorder = marked.erase.inorder := by
          rw [← movedEq]
          exact Marked.inorder_moveToRoot root marked
        have movedSkeleton : (MarkedTree.node left root right).skeleton.inorder =
            marked.skeleton.inorder := by
          rw [← movedEq, Marked.skeleton_moveToRoot, Tree.inorder_moveToRoot]
        have movedHoles : (MarkedTree.node left root right).holes = marked.holes := by
          rw [← movedEq]
          exact Marked.holes_moveToRoot root marked
        have movedOrdered : Ordered (MarkedTree.node left root right).erase := by
          unfold Ordered
          rw [movedInorder]
          exact ordered
        have movedKeys : ∀ key, key ∈ (MarkedTree.node left root right).erase.inorder ↔
            lo ≤ key ∧ key < hi := by
          intro key
          rw [movedInorder]
          exact keys key
        have movedSelected : ∀ key ∈ (MarkedTree.node left root right).erase.inorder,
            key ∈ (MarkedTree.node left root right).skeleton.inorder ↔ key ∈ row := by
          intro key member
          rw [movedSkeleton]
          exact selected key (movedInorder ▸ member)
        obtain ⟨orderedLeft, orderedRight, _, _⟩ := ordered_node_parts movedOrdered
        obtain ⟨_, keysLeft, keysRight⟩ := Marked.node_intervals movedOrdered movedKeys
        obtain ⟨selectedLeft, selectedRight⟩ := Marked.node_selected movedOrdered movedSelected
        have sizes : left.skeleton.size + 1 + right.skeleton.size = count := by
          have equal := congrArg List.length movedSkeleton
          have same : left.skeleton.size + 1 + right.skeleton.size = marked.skeleton.size := by
            simpa only [length_inorder, MarkedTree.skeleton, size] using equal
          exact same.trans sizeEq
        have holesLeft : ∀ tree ∈ left.holes, Heap height tree := by
          intro tree member
          apply holesHeap tree
          rw [← movedHoles]
          simp [MarkedTree.holes, member]
        have holesRight : ∀ tree ∈ right.holes, Heap height tree := by
          intro tree member
          apply holesHeap tree
          rw [← movedHoles]
          simp [MarkedTree.holes, member]
        obtain ⟨newLeft, leftSkeleton, leftHoles, leftInorder, leftHeap⟩ :=
          ih left.skeleton.size (by omega) (lo := lo) (hi := root)
            (by omega) left orderedLeft keysLeft selectedLeft holesLeft rfl
        obtain ⟨newRight, rightSkeleton, rightHoles, rightInorder, rightHeap⟩ :=
          ih right.skeleton.size (by omega) (lo := root+1) (hi := hi)
            upper right orderedRight keysRight selectedRight holesRight rfl
        refine ⟨.node newLeft root newRight, ?_, ?_, ?_, ?_⟩
        · simpa only [marked, MarkedTree.skeleton, inorder, leftSkeleton, rightSkeleton] using movedSkeleton
        · simpa only [marked, MarkedTree.holes, leftHoles, rightHoles] using movedHoles
        · simpa only [marked, MarkedTree.erase, inorder, leftInorder, rightInorder] using movedInorder
        · refine ⟨leftHeap, rightHeap, ?_, ?_⟩
          · intro key member
            rw [leftInorder] at member
            have bounds := (keysLeft key).mp member
            exact maximal key bounds.1 (bounds.2.trans rootHi)
          · intro key member
            rw [rightInorder] at member
            have bounds := (keysRight key).mp member
            exact maximal key (by omega) bounds.2

end DynamicOptimality.Geometry
