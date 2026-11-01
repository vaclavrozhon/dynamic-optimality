import TangoSquared.Paper20261030.OnlineStateAccounting

/-! Common-OPT accounting for the fixed prefix-consistent specification.
Its state and chosen transition are independent of future requests. The
specification remains noncomputable and carries a ghost component table;
this theorem does not replace the bounded local controller obligation. -/

namespace TangoSquared.Paper20261030.OnlineSpecification

open Rectangles SecondaryDecomposition LocalReferences DynamicOptimality

theorem canonical_word (H : Nat) :
    (Dyadic.canonical H 0).leaves = (List.range (2^H)).map (fun key : Nat => (key : Int)) := by
  apply List.Pairwise.eq_of_mem_iff (Dyadic.canonical_ordered H 0)
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_range).imp (fun smaller => by exact_mod_cast smaller)
  · intro key
    rw [Dyadic.canonical_zero_mem,List.mem_map]
    constructor
    · intro valid
      refine ⟨key.toNat,List.mem_range.mpr ?_,Int.toNat_of_nonneg valid.1⟩
      have bound : (key.toNat : Int) < (2 : Int)^H := by
        rw [Int.toNat_of_nonneg valid.1]
        exact valid.2
      exact_mod_cast bound
    · rintro ⟨rank,member,rfl⟩
      exact ⟨Int.natCast_nonneg _,by exact_mod_cast List.mem_range.mp member⟩

def rank {H : Nat} (request : Fin (Dyadic.canonical H 0).leaves.length) : Fin (2^H) :=
  ⟨request.val,by simpa only [canonical_word,List.length_map,List.length_range] using request.isLt⟩

theorem canonical_key {H : Nat} (request : Fin (Dyadic.canonical H 0).leaves.length) :
    key (Dyadic.canonical H 0).leaves request = ((rank request).val : Int) := by
  change (Dyadic.canonical H 0).leaves[request.val] = (request.val : Int)
  simp only [key,canonical_word,List.getElem_map,List.getElem_range,rank]

theorem canonical_OPT_cost (h : Nat)
    (requests : List (Fin (Dyadic.canonical (h+1) 0).leaves.length)) :
    (run (Dyadic.canonical_nodup _ _) (canonicalState (DepthTree.midpoint 0 h (Nat.zero_le h))) requests).2 ≤
      67440000000*(OPT (requests.map rank)+2^(h+1))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by
  let ref := DepthTree.midpoint 0 h (Nat.zero_le h)
  let actualKeys := requests.map (key (Dyadic.canonical (h+1) 0).leaves)
  let cost := (run (Dyadic.canonical_nodup _ _) (canonicalState ref) requests).2
  let factor := physicalRequestFactor ref
  have bound := canonical_cost ref requests
  change cost ≤ 7*(requests.length+13*robustBound (accessPoints actualKeys)+6*2^(h+1))*factor+3*requests.length at bound
  have same : actualKeys = (requests.map rank).map (fun request => (request.val : Int)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun request _ => canonical_key request)
  have lower := robustBound_le_shared_OPT (requests.map rank)
  rw [← same] at lower
  obtain ⟨_,_,rotations,_,optimum⟩ := OPT_attained (requests.map rank)
  have lengthBound : requests.length ≤ OPT (requests.map rank) := by
    rw [optimum,List.length_map]
    omega
  have positive : 1 ≤ factor := by simp only [factor,physicalRequestFactor]; omega
  have extra := Nat.mul_le_mul_left (3*requests.length) positive
  have coefficient : 7*(requests.length+13*robustBound (accessPoints actualKeys)+6*2^(h+1))+3*requests.length ≤
      6744*(OPT (requests.map rank)+2^(h+1)) := by omega
  change cost ≤ _
  calc
    cost ≤ (7*(requests.length+13*robustBound (accessPoints actualKeys)+6*2^(h+1))+3*requests.length)*factor := by
      rw [Nat.add_mul]
      omega
    _ ≤ 6744*(OPT (requests.map rank)+2^(h+1))*factor := Nat.mul_le_mul_right _ coefficient
    _ ≤ 6744*(OPT (requests.map rank)+2^(h+1))*(10000000*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1)) :=
      Nat.mul_le_mul_left _ (Dyadic.midpoint_request_factor h)
    _ = (6744*10000000)*(OPT (requests.map rank)+2^(h+1))*(Nat.clog 2 (Nat.clog 2 (h+1)+2)+1) := by ac_rfl
    _ = _ := rfl

end TangoSquared.Paper20261030.OnlineSpecification
