import ChaCha.Paper20261030.MemoryProjection
import ChaCha.Paper20261030.MixedMemories

/-!
# Mixed-block counts in the concrete memory histories

A reset block contains both Boolean directions. The exact owner-history
projection preserves this count, and the count for one request agrees
with the finite reset-key set used in the primary-flip charging argument.
-/

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection FlipAccounting

def wordReset (xs : List Bool) : Nat := if false ∈ xs ∧ true ∈ xs then 1 else 0

theorem false_mem_writeWord (c : Nat) (ds : List Nat) :
    false ∈ writeWord c ds ↔ lowDepths c ds ≠ [] := by
  constructor
  · intro h
    obtain ⟨d,hd,he⟩ := List.mem_map.mp h
    have hc : d ≤ c := by have := of_decide_eq_false he; omega
    have hm : d ∈ lowDepths c ds := List.mem_filter.mpr ⟨hd,by simpa using hc⟩
    intro hnil
    rw [hnil] at hm
    contradiction
  · intro h
    obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨hm,hc⟩ := List.mem_filter.mp hd
    have hc' : d ≤ c := of_decide_eq_true hc
    exact List.mem_map.mpr ⟨d,hm,by simp [show ¬ c < d by omega]⟩

theorem true_mem_writeWord (c : Nat) (ds : List Nat) :
    true ∈ writeWord c ds ↔ highDepths c ds ≠ [] := by
  constructor
  · intro h
    obtain ⟨d,hd,he⟩ := List.mem_map.mp h
    have hm : d ∈ highDepths c ds := List.mem_filter.mpr ⟨hd,he⟩
    intro hnil
    rw [hnil] at hm
    contradiction
  · intro h
    obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨hm,hc⟩ := List.mem_filter.mp hd
    exact List.mem_map.mpr ⟨d,hm,hc⟩

theorem wordReset_writeWord (c : Nat) (ds : List Nat) :
    wordReset (writeWord c ds) = ((visitBlock c ds).toList.map Block.resets).sum := by
  rw [visitBlock_resets]
  unfold wordReset
  simp only [false_mem_writeWord,true_mem_writeWord]
  by_cases hl : lowDepths c ds = [] <;> by_cases hr : highDepths c ds = [] <;> simp [hl,hr]

theorem mixed_iff_both (s : DepthSplit) (ds : List Nat) :
    Mixed s ds ↔
      false ∈ writeWord s.cut (intervalDepths s ds) ∧
      true ∈ writeWord s.cut (intervalDepths s ds) := by
  constructor
  · rintro ⟨e,he,f,hf,hsep⟩
    rcases hsep with ⟨ha,hc,hcf,hb⟩
    constructor
    · apply List.mem_map.mpr
      refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,?_⟩
      · simp only [decide_eq_true_eq]; omega
      · simp [show ¬ s.cut < e by omega]
    · apply List.mem_map.mpr
      refine ⟨f,List.mem_filter.mpr ⟨hf,?_⟩,?_⟩
      · simp only [decide_eq_true_eq]; omega
      · simpa using hcf
  · rintro ⟨he,hf⟩
    obtain ⟨e,hem,hec⟩ := List.mem_map.mp he
    obtain ⟨f,hfm,hfc⟩ := List.mem_map.mp hf
    obtain ⟨he,heab⟩ := List.mem_filter.mp hem
    obtain ⟨hf,hfab⟩ := List.mem_filter.mp hfm
    have heab' : s.lo ≤ e ∧ e ≤ s.hi := of_decide_eq_true heab
    have hfab' : s.lo ≤ f ∧ f ≤ s.hi := of_decide_eq_true hfab
    have hec' : ¬ s.cut < e := of_decide_eq_false hec
    have hfc' : s.cut < f := of_decide_eq_true hfc
    exact ⟨e,he,f,hf,heab'.1,by omega,hfc',hfab'.2⟩

variable {α : Type*} [DecidableEq α]

def resetHistory (primary : PrefRouter α) (key : MemoryKey) : List α → Nat
  | [] => 0
  | x :: xs => wordReset (requestWrites primary x key) + resetHistory (primary.access x) key xs

theorem ownerResetCount_cons (t : PrefRouter α) (c b : Nat) (x : α) (xs : List α) :
    ownerResetCount t c b (x :: xs) =
      wordReset (writeWord c (lowDepths b (t.exitDepths x))) + ownerResetCount (t.access x) c b xs := by
  simp only [ownerResetCount,ownerVisits,historyBlocks_cons,List.map_append,List.sum_append,
    wordReset_writeWord]

theorem resetHistory_owner {primary subtree : PrefRouter α} {s : DepthSplit} {u : List Bool}
    (hn : primary.leaves.Nodup) (hu : primary.atPath u = some subtree) (hlen : u.length = s.lo)
    (hc : s.lo ≤ s.cut) (hb : s.lo ≤ s.hi) (xs : List α)
    (hxs : ∀ x ∈ xs, x ∈ primary.leaves) :
    resetHistory primary (s,u) xs = ownerResetCount subtree (s.cut - s.lo) (s.hi - s.lo)
      (xs.filter (fun x => decide (x ∈ subtree.leaves))) := by
  induction xs generalizing primary subtree with
  | nil => rfl
  | cons x xs ih =>
    have hxglobal := hxs x (by simp)
    have hn' : (primary.access x).leaves.Nodup := by simpa only [PrefRouter.access_leaves] using hn
    have htail : ∀ y ∈ xs, y ∈ (primary.access x).leaves := by
      intro y hy
      simpa only [PrefRouter.access_leaves] using hxs y (by simp [hy])
    have hu' : (primary.access x).atPath u = some (subtree.access x) := by
      rw [PrefRouter.atPath_access primary hn x u,hu]
      rfl
    by_cases hx : x ∈ subtree.leaves
    · rw [resetHistory,requestWrites_atPath hn hu hlen hc hb hx,ih hn' hu' htail]
      simp only [List.filter_cons,decide_eq_true hx,↓reduceIte,ownerResetCount_cons,
        PrefRouter.access_leaves]
    · have habsent := subtree.access_absent x hx
      rw [habsent] at hu'
      rw [resetHistory,requestWrites_outside hn hu hxglobal hx,ih hn' hu' htail]
      simp only [List.filter_cons,decide_eq_false hx,Bool.false_eq_true,↓reduceIte,wordReset,
        List.not_mem_nil,false_and,if_false,Nat.zero_add]

theorem resetKeys_iff_wordReset {primary : PrefRouter α} {a b : Nat}
    {reference : DepthTree a b} {x : α} {key : MemoryKey}
    (hk : key ∈ memoryKeys primary reference) :
    key ∈ resetKeys primary reference x ↔ wordReset (requestWrites primary x key) = 1 := by
  classical
  simp only [resetKeys,Finset.mem_filter,hk,true_and,requestWrites]
  by_cases hp : key.2.IsPrefix (primary.searchPath x)
  · simp only [hp,true_and,if_pos,wordReset,← mixed_iff_both]
    split_ifs <;> simp_all
  · simp [hp,wordReset]

end ChaCha.Paper20261030.Secondary
