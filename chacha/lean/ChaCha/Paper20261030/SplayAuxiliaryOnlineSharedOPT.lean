import ChaCha.Paper20261030.SplayAuxiliaryOnline
import ChaCha.Paper20261030.OnlineSharedOPT

/-! The ordinary-splay online execution is compared with the existing
shared offline optimum, using the manuscript's repaired robust rectangle
lower bound and the same genuine secondary-memory accounting. -/

namespace ChaCha.Paper20261030.SplayAuxiliary.Online

open DynamicOptimality LocalReferences Rectangles

 theorem midpoint_accessFactor (h : Nat) :
    accessFactor (DepthTree.midpoint 0 h (Nat.zero_le h)) ≤
      60002*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  have height := completed_midpoint_height h
  have upper : (depthReference (completedDepth (DepthTree.midpoint 0 h (Nat.zero_le h)))).height ≤
      Nat.clog 2 (h+1)+2 := by rw [completedDepth_shape]; omega
  have logarithm := (Nat.log_le_clog 2 _).trans (Nat.clog_monotone 2 upper)
  unfold accessFactor requestFactor headFactor
  nlinarith

 theorem canonical_OPT_cost (h : Nat)
    (requests : List (Fin (Dyadic.canonical (h+1) 0).leaves.length)) :
    (run (Dyadic.canonical_ordered _ _) (canonicalState (DepthTree.midpoint 0 h (Nat.zero_le h))) requests).2 ≤
      60002000*(OPT (requests.map OnlineSpecification.rank)+2^(h+1))*
        (Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  let reference := DepthTree.midpoint 0 h (Nat.zero_le h)
  let actualKeys := requests.map (key (Dyadic.canonical (h+1) 0).leaves)
  have bound := canonical_cost reference requests
  have same : actualKeys = (requests.map OnlineSpecification.rank).map (fun request => (request.val : Int)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun request _ => OnlineSpecification.canonical_key request)
  have lower := robustBound_le_shared_OPT (requests.map OnlineSpecification.rank)
  rw [← same] at lower
  obtain ⟨_,_,rotations,_,optimum⟩ := OPT_attained (requests.map OnlineSpecification.rank)
  have lengthBound : requests.length ≤ OPT (requests.map OnlineSpecification.rank) := by
    rw [optimum,List.length_map]
    omega
  have coefficient : requests.length+13*robustBound (accessPoints actualKeys)+8*2^(h+1) ≤
      1000*(OPT (requests.map OnlineSpecification.rank)+2^(h+1)) := by omega
  calc
    _ ≤ (requests.length+13*robustBound (accessPoints actualKeys)+8*2^(h+1))*accessFactor reference := bound
    _ ≤ 1000*(OPT (requests.map OnlineSpecification.rank)+2^(h+1))*accessFactor reference :=
      Nat.mul_le_mul_right _ coefficient
    _ ≤ 1000*(OPT (requests.map OnlineSpecification.rank)+2^(h+1))*
        (60002*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1)) :=
      Nat.mul_le_mul_left _ (midpoint_accessFactor h)
    _ = _ := by ring

end ChaCha.Paper20261030.SplayAuxiliary.Online
