import ChaCha.Paper20261030.InitializedPhysicalBound
import ChaCha.Paper20261030.GapBSTAccess
import ChaCha.Paper20261030.ReferenceHeight
import DynamicOptimality.PointerInitialization

/-!
# Actual ordinary-BST traces with the geometric cost bound

The constructed source traces compile into the shared root-starting
pointer model, on exactly the original keys. An arbitrary initial BST
is rearranged to the encoded initial state with linear cost. This proves
trace existence, not yet execution by a bounded local online controller.
The latter must obtain the metadata used by the physical trace kernels.
-/

namespace ChaCha.Paper20261030.Dyadic

open ColoredStorage Rectangles Secondary SecondaryDecomposition LocalReferences PreferredProjection

theorem canonical_ordered (height : Nat) (owner : Int) :
    (canonical height owner).leaves.Pairwise (· < ·) := by
  induction height generalizing owner with
  | zero => simp [canonical,PrefRouter.leaves]
  | succ height ih =>
    apply List.pairwise_append.mpr
    refine ⟨ih _,ih _,?_⟩
    intro x hx y hy
    have left := (canonical_mem height (2*owner) x).mp hx
    have right := (canonical_mem height (2*owner+1) y).mp hy
    by_contra bad
    have monotone := Int.ediv_le_ediv (pow_pos (by decide : (0 : Int) < 2) height) (le_of_not_gt bad)
    omega

theorem bst_run_rectangle_bound {h : Nat} (reference : DepthTree 0 h)
    (before : MTR.Tree Int) (word : before.inorder = (canonical (h+1) 0).leaves)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    ∃ (after : MTR.Tree Int) (cost : Nat),
      after.inorder = before.inorder ∧ after.Ordered ∧ MTR.Pointer.Execution before requests after cost ∧
      cost ≤ (requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1))*physicalRequestFactor reference +
        3*requests.length+18*2^(h+1) := by
  have ordered : before.Ordered := by
    change before.inorder.Pairwise _
    rw [word]
    exact canonical_ordered _ _
  by_cases empty : requests = []
  · subst requests
    exact ⟨before,0,rfl,ordered,.nil _,Nat.zero_le _⟩
  · obtain ⟨_,after,_,sameLeaves,services⟩ := initialized_physical_rectangle_bound reference
      (initialPhysicalState reference) (initialPhysicalState_leaves reference) requests keys
    obtain ⟨cost,execution,bound⟩ := GapBST.services services
    have initialWord : before.inorder = (GapBST.encode (initialPhysicalState reference)).inorder := by
      rw [GapBST.encode_word,initialPhysicalState_leaves,word]
    obtain ⟨initialCost,initialTrace,initialBound⟩ := DynamicOptimality.initialize_pointer _ _ initialWord []
    have size : before.size = 2^(h+1) := by
      rw [← MTR.Tree.length_inorder,word]
      exact perfect_leaf_count (canonical_perfect (h+1) 0)
    have total := DynamicOptimality.prepend_pointer_initialization initialTrace execution empty
    have outWord : (GapBST.encode after).inorder = before.inorder := by
      rw [GapBST.encode_word,sameLeaves,initialPhysicalState_leaves,word]
    refine ⟨GapBST.encode after,initialCost+cost,outWord,?_,total,?_⟩
    · simpa only [MTR.Tree.Ordered,outWord] using ordered
    · rw [size] at initialBound
      omega

theorem midpoint_request_factor (h : Nat) :
    physicalRequestFactor (DepthTree.midpoint 0 h (Nat.zero_le h)) ≤
      10000000*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  have height := completed_midpoint_height h
  have logarithm := Nat.clog_monotone 2 (Nat.add_le_add_right height 1)
  unfold physicalRequestFactor
  rw [completedDepth_shape]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right logarithm 1)

theorem midpoint_bst_rectangle_bound {h : Nat} (before : MTR.Tree Int)
    (word : before.inorder = (canonical (h+1) 0).leaves)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    ∃ (after : MTR.Tree Int) (cost : Nat),
      after.inorder = before.inorder ∧ after.Ordered ∧ MTR.Pointer.Execution before requests after cost ∧
      cost ≤ 240000000 * (requests.length+rectangleBound (accessPoints requests)+2^(h+1)) *
        (Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  obtain ⟨after,cost,outWord,ordered,execution,bound⟩ := bst_run_rectangle_bound
    (DepthTree.midpoint 0 h (Nat.zero_le h)) before word requests keys
  refine ⟨after,cost,outWord,ordered,execution,?_⟩
  have factor := midpoint_request_factor h
  have weighted := Nat.mul_le_mul_left
    (requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1)) factor
  have logPositive : 1 ≤ Nat.clog 2 (Nat.clog 2 (h+1)+2)+1 := by omega
  have requestExtra := Nat.mul_le_mul_left (3*requests.length) logPositive
  have initialExtra := Nat.mul_le_mul_left (18*2^(h+1)) logPositive
  have coefficients :
      (requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1))*10000000 +
        3*requests.length+18*2^(h+1) ≤
      240000000*(requests.length+rectangleBound (accessPoints requests)+2^(h+1)) := by omega
  calc
    cost ≤ (requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1)) *
        (10000000*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1)) +
        3*requests.length*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) +
        18*2^(h+1)*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by omega
    _ = ((requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1))*10000000 +
        3*requests.length+18*2^(h+1)) * (Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
          simp only [Nat.add_mul,Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ coefficients

end ChaCha.Paper20261030.Dyadic
