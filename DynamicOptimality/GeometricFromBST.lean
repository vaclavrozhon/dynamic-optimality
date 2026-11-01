import DynamicOptimality.GeometricModel
import DynamicOptimality.HullSeparation

/-!
# Rooted-hull BST executions give arborally satisfied point sets

Each row is exactly the set of keys in the source hull. Last-touch times
form a weak max-heap in the current tree. Separation in that heap supplies
the third point of every new rectangle. No initial-tree charge is needed.
-/

namespace DynamicOptimality.Geometry

open TangoSquared TangoSquared.MTR TangoSquared.MTR.Tree
open TangoSquared.MTR.Tree.PriorityHull GreedyMerge.Geometry

noncomputable def hullRow {before after : RawTree Nat} {request : Nat}
    (access : HullAccess request before after) : Finset Nat := access.source.inorder.toFinset

theorem hull_row_card {before after : RawTree Nat} {request : Nat}
    (access : HullAccess request before after) (ordered : Ordered before) :
    (hullRow access).card = access.cost := by
  have sourceOrdered : Ordered access.source := ordered_of_graft (access.source_tree.symm ▸ ordered)
  have nodup : access.source.inorder.Nodup := sourceOrdered.imp (fun h => ne_of_lt h)
  simpa only [hullRow, List.toFinset_card_of_nodup nodup, length_inorder, HullAccess.cost]

theorem hull_row_satisfies {n : Nat} {before after : RawTree Nat} {request : Nat}
    (access : HullAccess request before after) (ordered : Ordered before)
    (keys : ∀ key, key ∈ before.inorder ↔ key < n)
    (height : Nat → Int) (heap : Heap height before) :
    RowSatisfies height n (hullRow access) := by
  have selected : ∀ key, key ∈ hullRow access ↔ key ∈ access.source.inorder := by
    intro key
    simp only [hullRow, List.mem_toFinset]
  constructor
  · intro key member
    apply (keys key).mp
    rw [← access.source_tree]
    exact (inorder_sublist_graft _ _ _).subset ((selected key).mp member)
  · intro start member old bound different
    have separation := hull_key_separation access.source access.gaps 0 height
      (access.source_tree.symm ▸ heap) (access.source_tree.symm ▸ ordered)
      ((selected start).mp member) (access.source_tree.symm ▸ (keys old).mpr bound)
    rcases separation with touched | recent | ⟨middle, inHull, notStart, notOld, lo, hi⟩
    · exact .inl ((selected old).mpr touched)
    · exact .inr (.inl ⟨start, ⟨min_le_left _ _, le_max_left _ _⟩, Ne.symm different, recent⟩)
    · exact .inr (.inr ⟨middle, (selected middle).mpr inHull, ⟨lo, hi⟩, notStart, notOld⟩)

theorem hull_row_heap {n : Nat} {before after : RawTree Nat} {request : Nat}
    (access : HullAccess request before after) (ordered : Ordered before)
    (keys : ∀ key, key ∈ before.inorder ↔ key < n)
    (height : Nat → Int) (time : Int) (heap : Heap height before)
    (above : ∀ key, key < n → height key < time) :
    Heap (update height time (hullRow access)) after := by
  have result := hull_touch_heap access ordered height time heap
    (fun key member => (above key ((keys key).mp member)).le)
  convert result using 1
  funext key
  simp only [update, hullRow, List.mem_toFinset, touchTime]

theorem hullExecution_surface {n : Nat} {before after : RawTree Nat}
    {requests : List Nat} {cost : Nat}
    (execution : AccessExecution before requests after cost)
    (ordered : Ordered before)
    (keys : ∀ key, key ∈ before.inorder ↔ key < n)
    (height : Nat → Int) (time : Int) (heap : Heap height before)
    (above : ∀ key, key < n → height key < time) :
    ∃ rows, SurfaceExecution n height time requests rows cost := by
  induction execution generalizing height time with
  | nil => exact ⟨[], .nil _ _⟩
  | @cons before middle after request requests cost access rest ih =>
    have valid := hull_row_satisfies access ordered keys height heap
    have nextHeap := hull_row_heap access ordered keys height time heap above
    have nextOrdered := access.ordered_after ordered
    have inorderEq : before.inorder = middle.inorder := by
      obtain ⟨_, _, trace⟩ := access.marked_trace ordered
      exact trace.rotations.inorder_eq
    have nextKeys : ∀ key, key ∈ middle.inorder ↔ key < n := by
      intro key
      rw [← inorderEq]
      exact keys key
    obtain ⟨rows, result⟩ := ih nextOrdered nextKeys _ (time+1) nextHeap (update_below_next above)
    refine ⟨hullRow access :: rows, ?_⟩
    have requested : request ∈ hullRow access := by
      simpa only [hullRow, List.mem_toFinset] using access.requested
    simpa only [hull_row_card access ordered] using SurfaceExecution.cons valid requested result

/-- Exact cost preservation from the existing rooted-hull model into the
pure geometric model, for every supplied initial BST on the original keys. -/
theorem of_hullExecution {n : Nat} {before after : RawTree Nat}
    {requests : List Nat} {cost : Nat}
    (execution : AccessExecution before requests after cost)
    (ordered : Ordered before)
    (keys : ∀ key, key ∈ before.inorder ↔ key < n) :
    Execution n requests cost := by
  apply execution_iff_surface.mpr
  exact hullExecution_surface execution ordered keys (fun _ => 0) 1
    (heap_uniform before _ 0 (by intros; rfl)) (by intros; omega)

end DynamicOptimality.Geometry
