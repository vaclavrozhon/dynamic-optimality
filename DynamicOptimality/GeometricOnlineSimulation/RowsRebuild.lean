import DynamicOptimality.GeometricOnlineSimulation.RowsSelected
import DynamicOptimality.GeometricOnlineSimulation.ClassDepth
import DynamicOptimality.ModelOnline

/-! # Rebuilding the current row as the new highest class -/

namespace DynamicOptimality.GeometricOnlineSimulation

open ChaCha.MTR SearchRotation

/-- Equal skeleton key sets can be rearranged at linear rotation cost. -/
private theorem skeleton_rotations (before after : RawTree Nat)
    (same : before.inorder = after.inorder) :
    ∃ count ≤ 6*before.size, Rotations before after count := by
  obtain ⟨count, bound, run⟩ := Tree.restricted_rotation_linear before after same
  have sizes : before.size = after.size := by
    simpa only [Tree.length_inorder] using congrArg List.length same
  exact ⟨count, by omega, OnlineModel.restrictedSteps_to_rotations run⟩

/-- The newly selected keys form one highest class. Its setup and physical
rearrangement cost are linear in the number of selected keys; all old holes
are retained unchanged. -/
theorem ClassFrame.Selected.rebuild {system : SplitTreeSystem} {height : Nat → Int}
    {row : Finset Nat} {time : Int} {lower upper : Nat}
    {skeleton : RawTree Nat} {frame : ClassFrame system skeleton}
    (selected : frame.Selected height row lower upper)
    (fresh : ∀ key, lower ≤ key → key < upper → height key < time)
    {request : Nat} (requested : request ∈ skeleton.inorder) :
    ∃ (tree : ClassTree system) (count depth : Nat),
      tree.Realizes (Geometry.update height time row) lower upper ∧
      Rotations frame.tree tree.tree count ∧
      count + tree.credit ≤ frame.credit + (system.K+6)*skeleton.size ∧
      Tree.searchDepth request tree.tree = some depth ∧ depth+1 ≤ skeleton.size := by
  let state := system.setup skeleton.inorder
  have keys : (system.tree state).inorder = skeleton.inorder := system.setup_keys _
  obtain ⟨count, countBound, run⟩ := skeleton_rotations skeleton (system.tree state) keys.symm
  obtain ⟨target, trace, sameCredit, selectedTarget⟩ :=
    ClassFrame.rotations_property run frame selected
  have targetRealizes := ClassFrame.Selected.retime selectedTarget fresh
  have nonempty : system.tree state ≠ .empty := by
    intro empty
    have targetMember : request ∈ (system.tree state).inorder := keys.symm ▸ requested
    simp only [empty, Tree.inorder, List.not_mem_nil] at targetMember
  have targetOrdered := selectedTarget.ordered_skeleton
  have targetMember : request ∈ (system.tree state).inorder := keys.symm ▸ requested
  obtain ⟨depth, found⟩ := Tree.searchDepth_exists_of_mem targetOrdered targetMember
  have depthBound := ChaCha.Paper20261030.SearchRotationBridge.searchDepth_lt_size found
  have sameSize : (system.tree state).size = skeleton.size := by
    simpa only [Tree.length_inorder] using congrArg List.length keys
  refine ⟨.node time state nonempty target, count, depth, .node targetRealizes, trace, ?_,
    target.searchDepth found, ?_⟩
  · have setupBound := system.setup_credit skeleton.inorder
    simp only [Tree.length_inorder] at setupBound
    simp only [ClassTree.credit]
    dsimp only [state] at sameCredit ⊢
    nlinarith
  · omega

/-- One causal step in the user's exact search-depth-plus-rotations model.
Twice the stored credit pays for the possible change in the initial search
depth as well as for all physical rotations. -/
theorem ClassTree.Realizes.row_access {system : SplitTreeSystem} {height : Nat → Int}
    {n : Nat} {row : Finset Nat} {time : Int} {tree : ClassTree system}
    (valid : tree.Realizes height 0 n)
    (fresh : ∀ key, key < n → height key < time)
    (satisfies : GreedyMerge.Geometry.RowSatisfies height n row)
    {request : Nat} (requested : request ∈ row) :
    ∃ (after : ClassTree system) (cost : Nat),
      after.Realizes (Geometry.update height time row) 0 n ∧
      Access request tree.tree after.tree cost ∧
      cost + 2*after.credit ≤ 2*tree.credit + (2*system.K+13)*row.card := by
  obtain ⟨skeleton, frame, extractCount, extractTrace, extractBudget, selected⟩ :=
    valid.extract satisfies (Nat.le_refl n)
  have member := (selected.mem_iff request).mpr ⟨Nat.zero_le _, satisfies.1 request requested, requested⟩
  obtain ⟨after, rebuildCount, depth, afterValid, rebuildTrace, rebuildBudget, found, depthBound⟩ :=
    selected.rebuild (fun key _ hi => fresh key hi) member
  have trace := extractTrace.append rebuildTrace
  obtain ⟨cost, legal, costBound⟩ :=
    RawDepth.access_of_final_depth trace valid.ordered request found
  have sizeBound := selected.size_le
  refine ⟨after, cost, afterValid, legal, ?_⟩
  nlinarith

end DynamicOptimality.GeometricOnlineSimulation
