import TangoSquared.Paper20261030.BSTRectangleBound
import TangoSquared.Paper20261030.GapBSTInitialization
import TangoSquared.Paper20261030.RobustCountingBound
import TangoSquared.Paper20261030.RobustBSTLowerBound

/-! Actual ordinary-BST trace comparison using the manuscript's robust
potential. The upper trace is the maintained Tango-squared source run;
the competitor is any actual execution in the shared pointer model.
The bounded local online controller remains a separate obligation. -/

namespace TangoSquared.Paper20261030.Dyadic

open Rectangles Secondary SecondaryDecomposition LocalReferences

theorem bst_run_robust_bound {h : Nat} (reference : DepthTree 0 h)
    (before : MTR.Tree Int) (word : before.inorder = (canonical (h+1) 0).leaves)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    ∃ (after : MTR.Tree Int) (cost : Nat), after.inorder = before.inorder ∧ after.Ordered ∧
      MTR.Pointer.Execution before requests after cost ∧
      cost ≤ (requests.length+13*robustBound (accessPoints requests)+6*2^(h+1))*physicalRequestFactor reference +
        3*requests.length+18*2^(h+1) := by
  let components := initialComponents (completedDepth reference) (canonical (h+1) 0)
    (canonical_perfect (h+1) 0) (fun _ => true)
  have valid := initialComponents_valid (completedDepth reference) (canonical (h+1) 0)
    (canonical_perfect (h+1) 0) (fun _ => true)
  have members : ∀ key ∈ requests, key ∈ (canonical (h+1) 0).leaves :=
    fun key member => (canonical_zero_mem _ _).mpr (keys key member)
  obtain ⟨_,out,_,physical⟩ := maintained_physical_run reference
    (MemoryState.initial (canonical (h+1) 0)) (canonical_perfect (h+1) 0) (canonical_nodup (h+1) 0)
    requests members components valid
  have work := abstract_work_robust_bound reference requests keys
  simp only [abstractWork,PreferredProjection.PrefRouter.depthAccessCount_eq,secondaryCost,MemoryState.initial] at work
  have budget : memoryCost (memoryKeys (canonical (h+1) 0) reference)
      (MemoryState.initial (canonical (h+1) 0)) requests + (canonical (h+1) 0).runFlips requests + requests.length ≤
      requests.length+13*robustBound (accessPoints requests)+6*2^(h+1) := by
    simpa only [MemoryState.initial] using (show _ ≤ _ by omega)
  have charged := physical.mono (Nat.mul_le_mul_right (physicalRequestFactor reference) budget)
  have initialWord : before.inorder = (physicalState (canonical (h+1) 0) components).shape.leaves :=
    word.trans (initialPhysicalState_leaves reference).symm
  obtain ⟨after,cost,finalWord,execution,bound⟩ := GapBST.services_from_tree before initialWord charged
  have size : before.size = 2^(h+1) := by
    rw [← MTR.Tree.length_inorder,word]
    exact perfect_leaf_count (canonical_perfect (h+1) 0)
  refine ⟨after,cost,finalWord,?_,execution,?_⟩
  · change after.inorder.Pairwise _
    rw [finalWord,word]
    exact canonical_ordered _ _
  · simpa only [size] using bound

theorem bst_versus_pointer {h : Nat} (before : MTR.Tree Int)
    (word : before.inorder = (canonical (h+1) 0).leaves)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key)
    {competitorStart competitorEnd : MTR.Tree Int} {competitorCost : Nat}
    (competitor : MTR.Pointer.Execution competitorStart requests competitorEnd competitorCost)
    (competitorOrdered : competitorStart.Ordered) :
    ∃ (after : MTR.Tree Int) (cost : Nat), after.inorder = before.inorder ∧ after.Ordered ∧
      MTR.Pointer.Execution before requests after cost ∧
      cost ≤ 300000000*(competitorCost+2^(h+1))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  obtain ⟨after,cost,finalWord,ordered,execution,bound⟩ :=
    bst_run_robust_bound (DepthTree.midpoint 0 h (Nat.zero_le h)) before word requests keys
  refine ⟨after,cost,finalWord,ordered,execution,?_⟩
  have rectangles := robustBound_le_pointer_cost competitor competitorOrdered
  obtain ⟨hullCost,hullBound,hull⟩ := competitor.toAccessExecution
  have lengthBound := hull.length_le_cost.trans hullBound
  let factor := physicalRequestFactor (DepthTree.midpoint 0 h (Nat.zero_le h))
  change cost ≤ (requests.length+13*robustBound (accessPoints requests)+6*2^(h+1))*factor +
    3*requests.length+18*2^(h+1) at bound
  have positive : 1 ≤ factor := by simp only [factor,physicalRequestFactor]; omega
  have extra := Nat.mul_le_mul_left (3*requests.length+18*2^(h+1)) positive
  have coefficients : requests.length+13*robustBound (accessPoints requests)+6*2^(h+1) +
      (3*requests.length+18*2^(h+1)) ≤ 30*(competitorCost+2^(h+1)) := by omega
  calc
    cost ≤ (requests.length+13*robustBound (accessPoints requests)+6*2^(h+1) +
        (3*requests.length+18*2^(h+1)))*factor := by
      rw [Nat.add_mul]
      omega
    _ ≤ 30*(competitorCost+2^(h+1))*factor := Nat.mul_le_mul_right _ coefficients
    _ ≤ 30*(competitorCost+2^(h+1))*(10000000*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1)) :=
      Nat.mul_le_mul_left _ (midpoint_request_factor h)
    _ = (30*10000000)*(competitorCost+2^(h+1))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by ac_rfl
    _ = _ := rfl

end TangoSquared.Paper20261030.Dyadic
