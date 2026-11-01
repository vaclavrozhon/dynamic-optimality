import TangoSquared.Paper20261030.PersistentMemory

/-!
# Counting actual mixed memories

An interval is mixed when two exit depths lie on opposite sides of its
split. Each mixed interval has at most one touched primary owner during
a request. This injects the actual reset memories into the branching
intervals of the visited depth reference.
-/

namespace TangoSquared.Paper20261030.Secondary

open PreferredProjection

def Mixed (s : DepthSplit) (ds : List Nat) : Prop :=
  ∃ e ∈ ds, ∃ f ∈ ds, s.Separates e f

attribute [local instance] Classical.propDecidable

noncomputable def mixedNodes {a b : Nat} (t : DepthTree a b) (ds : List Nat) : Finset DepthSplit :=
  t.nodes.filter (fun s => Mixed s ds)

theorem mixed_low_iff {s : DepthSplit} {c : Nat} (hb : s.hi ≤ c) (ds : List Nat) :
    Mixed s (lowDepths c ds) ↔ Mixed s ds := by
  constructor
  · rintro ⟨e,he,f,hf,hsep⟩
    exact ⟨e,(List.mem_filter.mp he).1,f,(List.mem_filter.mp hf).1,hsep⟩
  · rintro ⟨e,he,f,hf,hsep⟩
    refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,f,List.mem_filter.mpr ⟨hf,?_⟩,hsep⟩
    all_goals
      simp only [decide_eq_true_eq]
      rcases hsep with ⟨_,_,_,_⟩
      omega

theorem mixed_high_iff {s : DepthSplit} {c : Nat} (ha : c < s.lo) (ds : List Nat) :
    Mixed s (highDepths c ds) ↔ Mixed s ds := by
  constructor
  · rintro ⟨e,he,f,hf,hsep⟩
    exact ⟨e,(List.mem_filter.mp he).1,f,(List.mem_filter.mp hf).1,hsep⟩
  · rintro ⟨e,he,f,hf,hsep⟩
    refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,f,List.mem_filter.mpr ⟨hf,?_⟩,hsep⟩
    all_goals
      simp only [decide_eq_true_eq]
      rcases hsep with ⟨_,_,_,_⟩
      omega

theorem mixedNodes_low {a b c : Nat} (t : DepthTree a b) (hbc : b ≤ c) (ds : List Nat) :
    mixedNodes t (lowDepths c ds) = mixedNodes t ds := by
  ext s
  simp only [mixedNodes,Finset.mem_filter]
  by_cases hs : s ∈ t.nodes
  · have hb := (t.node_bounds hs).2.2.2
    simp only [hs,true_and,mixed_low_iff (hb.trans hbc)]
  · simp only [hs,false_and]

theorem mixedNodes_high {a b c : Nat} (t : DepthTree a b) (hca : c < a) (ds : List Nat) :
    mixedNodes t (highDepths c ds) = mixedNodes t ds := by
  ext s
  simp only [mixedNodes,Finset.mem_filter]
  by_cases hs : s ∈ t.nodes
  · have ha := (t.node_bounds hs).1
    simp only [hs,true_and,mixed_high_iff (lt_of_lt_of_le hca ha)]
  · simp only [hs,false_and]

theorem mixedNodes_bound {a b : Nat} (t : DepthTree a b) (ds : List Nat) :
    (mixedNodes t ds).card ≤ mixedVisits t ds := by
  induction t generalizing ds with
  | leaf a => simp [mixedNodes,DepthTree.nodes,mixedVisits]
  | @node a b c ha hb l r ihl ihr =>
    have hl := ihl (lowDepths c ds)
    have hr := ihr (highDepths c ds)
    rw [mixedNodes_low l le_rfl] at hl
    rw [mixedNodes_high r (by omega)] at hr
    have hunion := Finset.card_union_le (mixedNodes l ds) (mixedNodes r ds)
    have hinsert := Finset.card_insert_le (⟨a,c,b⟩ : DepthSplit)
      (mixedNodes l ds ∪ mixedNodes r ds)
    have heq : mixedNodes (.node c ha hb l r) ds =
        if Mixed ⟨a,c,b⟩ ds then insert ⟨a,c,b⟩ (mixedNodes l ds ∪ mixedNodes r ds)
        else mixedNodes l ds ∪ mixedNodes r ds := by
      simp only [mixedNodes,DepthTree.nodes,Finset.filter_insert,Finset.filter_union]
    rw [heq]
    by_cases hm : Mixed ⟨a,c,b⟩ ds
    · obtain ⟨e,he,f,hf,hsep⟩ := hm
      have hlo : lowDepths c ds ≠ [] := by
        intro h
        have : e ∈ lowDepths c ds := List.mem_filter.mpr ⟨he,by simpa using hsep.2.1⟩
        rw [h] at this
        contradiction
      have hhi : highDepths c ds ≠ [] := by
        intro h
        have : f ∈ highDepths c ds := List.mem_filter.mpr ⟨hf,by simpa using hsep.2.2.1⟩
        rw [h] at this
        contradiction
      rw [if_pos ⟨e,he,f,hf,hsep⟩]
      simp only [mixedVisits,hlo,hhi,false_or,if_false]
      omega
    · rw [if_neg hm]
      simp only [mixedVisits]
      split_ifs <;> omega

noncomputable def resetKeys {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    {a b : Nat} (reference : DepthTree a b) (x : α) : Finset MemoryKey :=
  (memoryKeys primary reference).filter
    (fun key => key.2.IsPrefix (primary.searchPath x) ∧ Mixed key.1 (primary.exitDepths x))

theorem resetKeys_injective {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    {a b : Nat} (reference : DepthTree a b) (x : α) :
    Set.InjOn Prod.fst (↑(resetKeys primary reference x) : Set MemoryKey) := by
  intro k hk j hj heq
  obtain ⟨hkm,hkp,hkx⟩ := Finset.mem_filter.mp hk
  obtain ⟨hjm,hjp,hjx⟩ := Finset.mem_filter.mp hj
  have hkl := (PrefRouter.mem_ownerPaths.mp ((mem_memoryKeys primary reference k.1 k.2).mp hkm).2).1
  have hjl := (PrefRouter.mem_ownerPaths.mp ((mem_memoryKeys primary reference j.1 j.2).mp hjm).2).1
  apply Prod.ext heq
  calc
    k.2 = (primary.searchPath x).take k.2.length := List.prefix_iff_eq_take.mp hkp
    _ = (primary.searchPath x).take j.2.length := by rw [hkl,hjl,heq]
    _ = j.2 := (List.prefix_iff_eq_take.mp hjp).symm

theorem resetKeys_card {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    {a b : Nat} (reference : DepthTree a b) (x : α) :
    (resetKeys primary reference x).card ≤ mixedVisits reference (primary.exitDepths x) := by
  have hinj := resetKeys_injective primary reference x
  have heq := Finset.card_image_iff.mpr hinj
  have hsub : (resetKeys primary reference x).image Prod.fst ⊆
      mixedNodes reference (primary.exitDepths x) := by
    intro s hs
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hkm,hkp,hkx⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨((mem_memoryKeys primary reference k.1 k.2).mp hkm).1,hkx⟩
  exact heq.symm ▸ (Finset.card_le_card hsub).trans (mixedNodes_bound reference _)

/-- Mixed genuine memories and a nontrivial completion-root visit together
cost at most one allowance per actual primary head switch. -/
theorem actual_reset_budget {α : Type*} [DecidableEq α] (primary : PrefRouter α)
    {a b : Nat} (reference : DepthTree a b) (x : α) :
    (resetKeys primary reference x).card + (if primary.exitDepths x = [] then 0 else 1) ≤
      primary.accessFlips x := by
  have hr := resetKeys_card primary reference x
  have hb := mixedVisits_bound reference (primary.exitDepths x)
  rw [PrefRouter.exitDepths_length] at hb
  omega

end TangoSquared.Paper20261030.Secondary
