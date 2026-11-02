import ChaCha.Paper20261030.DirectionScan

/-!
# Ordinary word alternations equal chronological switches

This is the primary-alternation counterpart of the active-direction scan.
It connects the actual primary branch words to the rectangle split bound.
-/

namespace ChaCha.Paper20261030.Rectangles

noncomputable def switchEventIndicator (P : Finset Point) (q : Point) : Nat :=
  by classical exact if SwitchPoint P q then 1 else 0

theorem switchPoint_iff_previous {P : Finset Point} (hP : Instance P)
    {p q : Point} (hn : Next P p q) : SwitchPoint P q ↔ p.1 ≠ q.1 := by
  constructor
  · rintro ⟨r,hr,hne⟩
    exact next_previous_unique hP hr hn ▸ hne
  · exact fun h => ⟨p,hn,h⟩

theorem switch_edge {P : Finset Point} (hP : Instance P)
    {p q : Point} (hn : Next P p q) : edgeChange p.1 q.1 = switchEventIndicator P q := by
  classical
  have he := switchPoint_iff_previous hP hn
  by_cases hk : p.1 = q.1 <;> simp [edgeChange,switchEventIndicator,he,hk]

theorem switch_scan_sum {P : Finset Point} (hP : Instance P)
    (p : Point) (ps : List Point) (hchain : (p :: ps).IsChain (Next P)) :
    changesFrom p.1 (ps.map Prod.fst) = (ps.map (switchEventIndicator P)).sum := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    obtain ⟨hn,ht⟩ := List.isChain_cons_cons.mp hchain
    simp only [List.map_cons,changesFrom_cons,List.sum_cons,switch_edge hP hn,ih q ht]

theorem alternations_switchCount (ps : List Point) (hs : Chronological ps) :
    alternations (ps.map Prod.fst) = switchCount ps.toFinset := by
  classical
  cases ps with
  | nil => simp [switchCount,eventCount]
  | cons p ps =>
    have hP := chronological_instance hs
    have hzero : switchEventIndicator (p :: ps).toFinset p = 0 := by
      have hno : ¬ SwitchPoint (p :: ps).toFinset p := by
        rintro ⟨q,hq,_⟩
        have := chronological_first hs q hq.1
        have := hq.2.2.1
        omega
      simp only [switchEventIndicator,if_neg hno]
    rw [List.map_cons,alternations,switch_scan_sum hP p ps (chronological_chain hs)]
    change _ = ∑ q ∈ (p :: ps).toFinset, switchEventIndicator (p :: ps).toFinset q
    rw [sum_toFinset_word (chronological_nodup hs),List.map_cons,List.sum_cons,hzero,Nat.zero_add]

theorem changesFrom_injective_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (a : α) (xs : List α) :
    changesFrom (f a) (xs.map f) = changesFrom a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,changesFrom_cons,edgeChange,hf.eq_iff,ih]

theorem alternations_injective_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    alternations (xs.map f) = alternations xs := by
  cases xs with
  | nil => rfl
  | cons a xs => exact changesFrom_injective_map f hf a xs

end ChaCha.Paper20261030.Rectangles
