import TangoSquared.Paper20261030.ResetHistories
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Global flip accounting for the concrete persistent-memory algorithm

The LCA count here is computed from consecutive requests at the actual
primary owners. Summing the exact bit histories and the injective reset
budget proves the manuscript's numerical secondary-flip inequality.
Identifying this tree-based count with the dyadic rectangle theorem and
realizing the bit-array operations by physical BST steps remain separate.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def keyLCA (primary : PrefRouter α) (key : MemoryKey) (xs : List α) : Nat :=
  match primary.atPath key.2 with
  | none => 0
  | some subtree => localLCAAlternations subtree (key.1.cut - key.1.lo) (key.1.hi - key.1.lo)
      (xs.filter (fun x => decide (x ∈ subtree.leaves)))

def memoryLCA (primary : PrefRouter α) {a b : Nat} (reference : DepthTree a b) (xs : List α) : Nat :=
  ∑ key ∈ memoryKeys primary reference, keyLCA primary key xs

theorem key_flip_bound {primary : PrefRouter α} {H a b : Nat}
    (hp : primary.Perfect H) (hn : primary.leaves.Nodup) (reference : DepthTree a b)
    (hb : b < H) {key : MemoryKey} (hk : key ∈ memoryKeys primary reference)
    (initial : Bool) (xs : List α) (hxs : ∀ x ∈ xs, x ∈ primary.leaves) :
    changesFrom initial (bitHistory primary key xs) ≤
      2 * keyLCA primary key xs + 2 * resetHistory primary key xs + 3 := by
  obtain ⟨hnode,howner⟩ := (mem_memoryKeys primary reference key.1 key.2).mp hk
  obtain ⟨hlen,subtree,hu⟩ := PrefRouter.mem_ownerPaths.mp howner
  obtain ⟨_,hc,hcb,hhi⟩ := reference.node_bounds hnode
  have h := memory_key_flip_bound hp hn hu hlen hc hcb (hhi.trans_lt hb) initial xs hxs
  rw [← resetHistory_owner hn hu hlen hc (by omega) xs hxs] at h
  simpa only [keyLCA,hu] using h

theorem sum_request_resets (primary : PrefRouter α) {a b : Nat}
    (reference : DepthTree a b) (x : α) :
    (∑ key ∈ memoryKeys primary reference, wordReset (requestWrites primary x key)) =
      (resetKeys primary reference x).card := by
  classical
  let P := fun key : MemoryKey =>
    key.2.IsPrefix (primary.searchPath x) ∧ Mixed key.1 (primary.exitDepths x)
  change _ = ((memoryKeys primary reference).filter P).card
  have hboole : (∑ key ∈ memoryKeys primary reference, if P key then 1 else 0) =
      ((memoryKeys primary reference).filter P).card := by
    simpa using (Finset.sum_boole (R := Nat) P (memoryKeys primary reference))
  rw [← hboole]
  apply Finset.sum_congr rfl
  intro key hk
  have he := resetKeys_iff_wordReset (x := x) hk
  have hm : key ∈ resetKeys primary reference x ↔ P key := by
    simp only [resetKeys,Finset.mem_filter,hk,true_and,P]
  by_cases h : P key
  · rw [if_pos h]
    exact he.mp (hm.mpr h)
  · rw [if_neg h]
    have hne : wordReset (requestWrites primary x key) ≠ 1 := fun hh => h (hm.mp (he.mpr hh))
    unfold wordReset at *
    split_ifs at * <;> omega

/-- All extra mixed-block charges, including the completion-root flips,
are paid by actual primary switches. -/
theorem reset_history_budget (primary : PrefRouter α) {a b : Nat}
    (reference : DepthTree a b) (xs : List α) :
    2 * (∑ key ∈ memoryKeys primary reference, resetHistory primary key xs) +
      completionCost primary xs ≤ 2 * primary.runFlips xs := by
  induction xs generalizing primary with
  | nil => simp [resetHistory,completionCost,PrefRouter.runFlips]
  | cons x xs ih =>
    have hi := ih (primary.access x)
    rw [memoryKeys_access] at hi
    have hb := actual_reset_budget primary reference x
    simp only [resetHistory,Finset.sum_add_distrib,sum_request_resets,
      completionCost,completionWord_cost,PrefRouter.runFlips]
    by_cases he : primary.exitDepths x = []
    · simp only [if_pos he] at hb ⊢
      omega
    · simp only [if_neg he] at hb ⊢
      omega

theorem memoryCost_bound {H a b : Nat} (reference : DepthTree a b) (s : MemoryState α)
    (hp : s.primary.Perfect H) (hn : s.primary.leaves.Nodup) (hb : b < H)
    (xs : List α) (hxs : ∀ x ∈ xs, x ∈ s.primary.leaves) :
    memoryCost (memoryKeys s.primary reference) s xs ≤
      2 * memoryLCA s.primary reference xs +
      2 * (∑ key ∈ memoryKeys s.primary reference, resetHistory s.primary key xs) +
      3 * (memoryKeys s.primary reference).card := by
  rw [memoryCost_eq_histories]
  have h := Finset.sum_le_sum (fun key hk =>
    key_flip_bound hp hn reference hb hk (s.preference key) xs hxs)
  simpa only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,
    Nat.nsmul_eq_mul,Nat.mul_comm,memoryLCA] using h

theorem secondaryCost_bound {H a b : Nat} (reference : DepthTree a b) (s : MemoryState α)
    (hp : s.primary.Perfect H) (hn : s.primary.leaves.Nodup) (hb : b < H)
    (xs : List α) (hxs : ∀ x ∈ xs, x ∈ s.primary.leaves) :
    secondaryCost reference s xs ≤ 2 * memoryLCA s.primary reference xs +
      2 * s.primary.runFlips xs + 3 * (memoryKeys s.primary reference).card := by
  have hm := memoryCost_bound reference s hp hn hb xs hxs
  have hr := reset_history_budget s.primary reference xs
  unfold secondaryCost
  omega

theorem perfect_leaf_count {H : Nat} {primary : PrefRouter α} (hp : primary.Perfect H) :
    primary.leaves.length = 2 ^ H := by
  induction H generalizing primary with
  | zero => cases primary <;> simp_all [PrefRouter.Perfect,PrefRouter.leaves]
  | succ H ih =>
    cases primary with
    | leaf a => contradiction
    | fork b l r =>
      simp only [PrefRouter.leaves,List.length_append,ih hp.1,ih hp.2,pow_succ]
      omega

/-- The concrete algorithm's secondary-flip estimate, with the manuscript's
constants. The LCA term still uses actual tree-based owner histories. -/
theorem secondary_flip_bound {h : Nat} (reference : DepthTree 0 h) (s : MemoryState α)
    (hp : s.primary.Perfect (h + 1)) (hn : s.primary.leaves.Nodup)
    (xs : List α) (hxs : ∀ x ∈ xs, x ∈ s.primary.leaves) :
    secondaryCost reference s xs ≤ 2 * memoryLCA s.primary reference xs +
      2 * s.primary.primaryWilber xs + 5 * s.primary.internalVertices := by
  have hsecondary := secondaryCost_bound reference s hp hn (by omega) xs hxs
  have hprimary := s.primary.primary_flip_bound xs
  have hkeys := root_memoryKeys_card hp reference
  have hleaves := perfect_leaf_count hp
  have hvertices := s.primary.internal_vertices_leaves
  rw [pow_succ] at hleaves
  omega

end TangoSquared.Paper20261030.Secondary
