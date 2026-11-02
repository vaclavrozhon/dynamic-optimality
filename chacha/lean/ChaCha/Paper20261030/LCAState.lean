import ChaCha.Paper20261030.FragmentDecomposition

/-!
# Agreement with the LCA update rule

This is a direct bridge from consecutive original accesses to the fragment
state. An LCA below the fragment leaves its state unchanged; an LCA in its
lower part sets DOWN; an LCA in its upper part sets UP.
-/

namespace ChaCha.Paper20261030.Dyadic

open Rectangles

theorem coarsen_valid {b c : Nat} (hcb : c ≤ b) {x : Int} (hx : ValidKey b x) :
    ValidKey c (coarsen b c x) := by
  have hpos : (0 : Int) < 2 ^ (b - c) := pow_pos (by decide) _
  constructor
  · exact Int.ediv_nonneg hx.1 hpos.le
  · apply Int.ediv_lt_of_lt_mul hpos
    have he : (2 : Int) ^ c * 2 ^ (b - c) = 2 ^ b := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    exact hx.2

theorem lca_update_rule {H c b : Nat} {P : Finset Point} (hP : Instance P)
    {p q : Point} (hpq : Next P p q) (hp : ValidKey H p.1) (hq : ValidKey H q.1)
    (hcb : c ≤ b) (hbH : b ≤ H) :
    ActiveDown (project (coarsen H b) P) (coarsen b c) (mapPoint (coarsen H b) q) ↔
      if b ≤ lcaDepth H p.1 q.1 then
        ActiveDown (project (coarsen H b) P) (coarsen b c) (mapPoint (coarsen H b) p)
      else c ≤ lcaDepth H p.1 q.1 := by
  have hproj := instance_project hP (coarsen H b)
  have hn := next_project (coarsen H b) hpq
  by_cases hdeep : b ≤ lcaDepth H p.1 q.1
  · rw [if_pos hdeep]
    apply activeDown_repeat hproj (coarsen b c) hn
    exact (ancestor_eq_iff_le_lca hp hq hbH).mpr hdeep
  · rw [if_neg hdeep]
    have hneq : (mapPoint (coarsen H b) p).1 ≠ (mapPoint (coarsen H b) q).1 := by
      exact fun he => hdeep ((ancestor_eq_iff_le_lca hp hq hbH).mp he)
    rw [activeDown_change hproj (coarsen b c) hn hneq]
    change coarsen b c (coarsen H b p.1) = coarsen b c (coarsen H b q.1) ↔ _
    rw [coarsen_comp hcb hbH,coarsen_comp hcb hbH]
    exact ancestor_eq_iff_le_lca hp hq (hcb.trans hbH)

theorem projected_downUp_iff_lca {H c b : Nat} {P : Finset Point} (hP : Instance P)
    (hkeys : ∀ p ∈ P, ValidKey H p.1) (hcb : c ≤ b) (hbH : b ≤ H)
    {q : Point} (hq : q ∈ P) :
    DownUpAt (project (coarsen H b) P) (coarsen b c) (mapPoint (coarsen H b) q) ↔
      ∃ p, Next P p q ∧
        ActiveDown (project (coarsen H b) P) (coarsen b c) (mapPoint (coarsen H b) p) ∧
        lcaDepth H p.1 q.1 < c := by
  constructor
  · rintro ⟨v,hvq,hstate⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hvq.1
    have hn := next_of_project (coarsen H b) hp hq hvq
    have hchange := (downUp_iff_exit_edge (instance_project hP (coarsen H b))
      (coarsen b c) hvq).mp hstate
    have hne := hchange.2
    change coarsen b c (coarsen H b p.1) ≠ coarsen b c (coarsen H b q.1) at hne
    rw [coarsen_comp hcb hbH,coarsen_comp hcb hbH] at hne
    have hlt : lcaDepth H p.1 q.1 < c := by
      have hiff := ancestor_eq_iff_le_lca (hkeys p hp) (hkeys q hq) (hcb.trans hbH)
      omega
    exact ⟨p,hn,hchange.1,hlt⟩
  · rintro ⟨p,hn,hstate,hlt⟩
    have hne : coarsen b c (coarsen H b p.1) ≠ coarsen b c (coarsen H b q.1) := by
      rw [coarsen_comp hcb hbH,coarsen_comp hcb hbH]
      intro he
      have := (ancestor_eq_iff_le_lca (hkeys p hn.1) (hkeys q hq) (hcb.trans hbH)).mp he
      omega
    exact ⟨mapPoint (coarsen H b) p,next_project (coarsen H b) hn,
      (downUp_iff_exit_edge (instance_project hP (coarsen H b)) (coarsen b c)
        (next_project (coarsen H b) hn)).mpr ⟨hstate,hne⟩⟩

/-- An actual LCA transition count, expressed on the original time rows. -/
noncomputable def lcaTransitions (H c b : Nat) (P : Finset Point) : Nat :=
  eventCount P (fun q => ∃ p, Next P p q ∧
    ActiveDown (project (coarsen H b) P) (coarsen b c) (mapPoint (coarsen H b) p) ∧
    lcaDepth H p.1 q.1 < c)

theorem lcaTransitions_eq_depthAlternations {H c b : Nat} {P : Finset Point}
    (hP : Instance P) (hkeys : ∀ p ∈ P, ValidKey H p.1) (hcb : c ≤ b) (hbH : b ≤ H) :
    lcaTransitions H c b P = depthAlternations (project (coarsen H b) P) (coarsen b c) := by
  rw [depthAlternations_eq_downUp (instance_project hP (coarsen H b)),eventCount_project hP]
  unfold lcaTransitions eventCount
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only
  have he := projected_downUp_iff_lca hP hkeys hcb hbH hq
  by_cases hd : DownUpAt (project (coarsen H b) P) (coarsen b c) (mapPoint (coarsen H b) q)
  · simp only [if_pos hd,if_pos (he.mp hd)]
  · simp only [if_neg hd,if_neg (fun h => hd (he.mpr h))]

end ChaCha.Paper20261030.Dyadic
