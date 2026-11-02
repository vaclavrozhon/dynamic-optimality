import CanonicalSurface
import DynamicOptimality.HullPriorityUpdate

/-! # An indexed BST heap for any geometric surface

The existing canonical Cartesian refinement supplies an actual indexed tree
on the original interval. Forgetting its tie-breaking conditions gives the
weak max-heap needed to start backwards geometric reconstruction.
-/

namespace DynamicOptimality.Geometry

open ChaCha.MTR.Tree.PriorityHull

theorem canonical_raw_heap {lower upper : Nat} {height : Nat → Int} {priority : Nat → Nat}
    (tree : BST lower upper) (canonical : GreedyMerge.Surface.Canonical height priority tree) :
    Heap height tree.toRaw := by
  induction tree with
  | empty => trivial
  | @node lower root upper left right ihLeft ihRight =>
    refine ⟨ihLeft canonical.2.2.2.1, ihRight canonical.2.2.2.2, ?_, ?_⟩
    · intro key member
      obtain ⟨lo, hi⟩ := (BST.toRaw_mem left).mp member
      have outer := right.lower_le_upper
      exact canonical.1 key lo (by omega)
    · intro key member
      obtain ⟨lo, hi⟩ := (BST.toRaw_mem right).mp member
      have outer := left.lower_le_upper
      exact canonical.1 key (by omega) hi

theorem exists_heap_indexed (height : Nat → Int) (n : Nat) :
    ∃ tree : BST 0 n, Heap height tree.toRaw := by
  obtain ⟨tree, canonical⟩ := GreedyMerge.Surface.exists_canonical height (fun _ => 0)
    0 n (Nat.zero_le n)
  exact ⟨tree, canonical_raw_heap tree canonical⟩

end DynamicOptimality.Geometry
