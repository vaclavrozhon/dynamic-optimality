import ChaCha.Paper20261030.TurnExistence

/-!
# Magnitude of the manuscript's concrete potential

`potential` is the actual robust rectangle maximum, minus the weighted
switch and turn counts. Its nonnegativity is proved from input events.
-/

namespace ChaCha.Paper20261030.Rectangles

attribute [local instance] Classical.propDecidable

theorem turnPoint_switchPoint {P : Finset Point} {r : Point}
    (h : TurnPoint P r) : SwitchPoint P r := by
  obtain ⟨p,q,hqr,hpq,ht⟩ := h
  exact ⟨q,hqr,by have := ht.2.2; omega⟩

theorem turnPoint_earlier_switch {P : Finset Point} (hP : Instance P)
    {r : Point} (h : TurnPoint P r) : ∃ s ∈ P, s.2 < r.2 ∧ SwitchPoint P s := by
  obtain ⟨p,q,hqr,hpq,ht⟩ := h
  obtain ⟨s,hps⟩ := exists_successor hpq.1 ⟨q,hpq.2.1,hpq.2.2.1⟩
  have hsq := successor_le hps hpq.2.1 hpq.2.2.1
  have hsr := lt_of_le_of_lt hsq hqr.2.2.1
  have hsk := turn_plateau hP hpq hqr hps.2.1 hps.2.2.1 hsr
  exact ⟨s,hps.2.1,hsr,p,hps,by simpa only [hsk] using hpq.2.2.2.1⟩

noncomputable def switchIndicator (P : Finset Point) : Nat :=
  if 0 < switchCount P then 1 else 0

theorem turns_indicator_le_switches {P : Finset Point} (hP : Instance P) :
    turnCount P + switchIndicator P ≤ switchCount P := by
  classical
  let T := P.filter (TurnPoint P)
  let S := P.filter (SwitchPoint P)
  have hsub : T ⊆ S := by
    intro r hr
    obtain ⟨hrP,ht⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hrP,turnPoint_switchPoint ht⟩
  have htc : T.card = turnCount P := (eventCount_eq_card P (TurnPoint P)).symm
  have hsc : S.card = switchCount P := (eventCount_eq_card P (SwitchPoint P)).symm
  by_cases hpos : 0 < switchCount P
  · have hne : S.Nonempty := Finset.card_pos.mp (hsc.symm ▸ hpos)
    obtain ⟨r,hr,hmin⟩ := Finset.exists_min_image S Prod.snd hne
    have hrnot : r ∉ T := by
      intro ht
      obtain ⟨s,hs,hsr,hsw⟩ := turnPoint_earlier_switch hP (Finset.mem_filter.mp ht).2
      have := hmin s (Finset.mem_filter.mpr ⟨hs,hsw⟩)
      omega
    have hstrict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro he
      exact hrnot (he.symm ▸ hr)⟩
    have hlt := Finset.card_lt_card hstrict
    simp only [switchIndicator,if_pos hpos]
    omega
  · have hle := Finset.card_le_card hsub
    simp only [switchIndicator,if_neg hpos]
    omega

noncomputable def potential (P : Finset Point) : Int :=
  5 * (robustBound P : Int) - 4 * (switchCount P : Int) -
    (turnCount P : Int) - (switchIndicator P : Int)

theorem potential_nonnegative {P : Finset Point} (hP : Instance P) :
    0 ≤ potential P := by
  have h₁ := turns_indicator_le_switches hP
  have h₂ := switchCount_le_robustBound hP
  unfold potential
  omega

theorem potential_le_rectangleBound (P : Finset Point) :
    potential P ≤ 5 * (rectangleBound P : Int) := by
  have := robustBound_le_rectangleBound P
  unfold potential
  omega

end ChaCha.Paper20261030.Rectangles
