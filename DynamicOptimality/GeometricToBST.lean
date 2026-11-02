import DynamicOptimality.GeometricToBSTRepair
import DynamicOptimality.GeometricToBSTPrefix
import DynamicOptimality.GeometricToBSTHeap
import DynamicOptimality.ModelOnline

/-!
# Arborally satisfied geometry has an ordinary BST realization

The construction runs backwards through the geometric rows. The most
recent row is a rooted prefix of the current last-touch heap; repairing
only that prefix recovers a heap for the preceding surface. Thus every
geometric row becomes an actual rooted-hull access at exactly its point
count, on the original keys. The initial tree is freely chosen. This
existence theorem is offline: its tree choices can depend on later rows.
-/

namespace DynamicOptimality.Geometry

open ChaCha ChaCha.MTR ChaCha.MTR.Tree
open ChaCha.MTR.Pointer ChaCha.MTR.Tree.PriorityHull
open GreedyMerge.Geometry

theorem row_repair {n request : Nat} {height : Nat → Int} {time : Int}
    {row : Finset Nat} (satisfied : RowSatisfies height n row)
    (requested : request ∈ row) (after : RawTree Nat)
    (ordered : Ordered after) (keys : ∀ key, key ∈ after.inorder ↔ key < n)
    (heap : Heap (update height time row) after)
    (above : ∀ key, key < n → height key < time) :
    ∃ before : RawTree Nat, Heap height before ∧ before.inorder = after.inorder ∧
      ∃ access : HullAccess request before after, access.cost = row.card := by
  classical
  let marked := markRow row after
  have markedOrdered : Ordered marked.erase := by simpa [marked] using ordered
  have markedKeys : ∀ key, key ∈ marked.erase.inorder ↔ 0 ≤ key ∧ key < n := by
    intro key
    simpa [marked] using keys key
  have bounded : ∀ key ∈ after.inorder, key < n := fun key member => (keys key).mp member
  have markedMembers := markRow_members after heap bounded above
  have selected : ∀ key ∈ marked.erase.inorder,
      key ∈ marked.skeleton.inorder ↔ key ∈ row := by
    intro key member
    have original : key ∈ after.inorder := by simpa [marked] using member
    simp only [marked, markedMembers, original, and_true]
  have holesHeap := markRow_holes_heap after heap bounded above
  obtain ⟨repaired, sameKeys, sameHoles, sameInorder, repairedHeap⟩ :=
    repair_marked satisfied (le_refl n) marked markedOrdered markedKeys selected holesHeap
  have beforeInorder : repaired.erase.inorder = after.inorder := by
    simpa [marked] using sameInorder
  have repairedMembers : ∀ key, key ∈ repaired.skeleton.inorder ↔ key ∈ row := by
    intro key
    rw [sameKeys]
    change key ∈ (markRow row after).skeleton.inorder ↔ key ∈ row
    rw [markedMembers]
    exact ⟨And.left, fun member => ⟨member, (keys key).mpr (satisfied.1 key member)⟩⟩
  let access : HullAccess request repaired.erase after := {
    source := repaired.skeleton
    target := marked.skeleton
    gaps := repaired.gapArray
    source_tree := repaired.graft_gapArray
    target_tree := by
      have gapEq : repaired.gapArray = marked.gapArray := by
        funext index
        simp only [MarkedTree.gapArray, sameHoles]
      rw [gapEq, marked.graft_gapArray]
      exact markRow_erase row after
    same_keys := sameKeys
    requested := (repairedMembers request).mpr requested }
  have beforeOrdered : Ordered repaired.erase := by
    unfold Ordered
    rw [beforeInorder]
    exact ordered
  have skeletonOrdered : Ordered repaired.skeleton :=
    List.Pairwise.sublist (Marked.skeleton_sublist repaired) beforeOrdered
  have nodup : repaired.skeleton.inorder.Nodup := skeletonOrdered.imp (fun h => ne_of_lt h)
  have finiteSet : repaired.skeleton.inorder.toFinset = row := by
    ext key
    simpa only [List.mem_toFinset] using repairedMembers key
  refine ⟨repaired.erase, repairedHeap, beforeInorder, access, ?_⟩
  change repaired.skeleton.size = row.card
  rw [← length_inorder, ← List.toFinset_card_of_nodup nodup, finiteSet]

/-- Backwards reconstruction preserves the exact number of geometric points.
The initial heap is a conclusion, so it can be reused for the preceding row. -/
theorem SurfaceExecution.to_hull {n : Nat} {height : Nat → Int} {time : Int}
    {requests : List Nat} {rows : List (Finset Nat)} {cost : Nat}
    (execution : SurfaceExecution n height time requests rows cost)
    (above : ∀ key, key < n → height key < time) :
    ∃ before after : RawTree Nat,
      Ordered before ∧ before.inorder = List.range n ∧ Heap height before ∧
        AccessExecution before requests after cost := by
  induction execution with
  | nil height time =>
      obtain ⟨tree, heap⟩ := exists_heap_indexed height n
      exact ⟨tree.toRaw, tree.toRaw, tree.toRaw_ordered,
        OnlineModel.indexed_inorder tree, heap, .nil _⟩
  | @cons height time requests rows cost request row satisfied requested rest ih =>
      obtain ⟨middle, after, ordered, keys, heap, tail⟩ := ih (update_below_next above)
      have keyMembership : ∀ key, key ∈ middle.inorder ↔ key < n := by
        intro key
        rw [keys, List.mem_range]
      obtain ⟨before, beforeHeap, beforeInorder, access, charge⟩ :=
        row_repair satisfied requested middle ordered keyMembership heap above
      have beforeOrdered : Ordered before := by
        unfold Ordered
        rw [beforeInorder]
        exact ordered
      refine ⟨before, after, beforeOrdered, beforeInorder.trans keys, beforeHeap, ?_⟩
      simpa only [charge] using AccessExecution.cons access tail

/-- Every pure arborally satisfied geometric execution has an exact-cost
rooted-hull BST execution, with no dummy keys or assumed simulation witness. -/
theorem to_hullExecution {n : Nat} {requests : List Nat} {cost : Nat}
    (execution : Execution n requests cost) :
    ∃ (initial : BST 0 n) (final : RawTree Nat),
      AccessExecution initial.toRaw requests final cost := by
  obtain ⟨rows, surface⟩ := execution_iff_surface.mp execution
  obtain ⟨before, after, _, keys, _, actual⟩ :=
    surface.to_hull (by intros; omega)
  obtain ⟨initial, initialEq⟩ := OnlineModel.indexed_of_inorder before keys
  exact ⟨initial, after, initialEq ▸ actual⟩

end DynamicOptimality.Geometry
