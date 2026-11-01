import TangoSquared.ArboralGrowingCap

/-!
# Preparing a smaller cap before hiding a suffix

If an arborally satisfied history touches (d, tau), one may clamp all
LATER rows to d while leaving the preparation row and the past intact.
This is one safe shrink. It does not assert that a later unclipping is safe.
-/

namespace TangoSquared.ArboralCapSplice

open ArboralDilation ArboralQuotient ArboralGrowingCap

def clipAfter (d tau : Int) (P : Finset Point) : Finset Point :=
  P.image (fun p => (if tau < p.2 then min p.1 d else p.1, p.2))

theorem mem_clipAfter {d tau a t : Int} {P : Finset Point} :
    (a, t) ∈ clipAfter d tau P ↔
      ∃ x, (x, t) ∈ P ∧ (if tau < t then min x d else x) = a := by
  constructor
  · intro h
    obtain ⟨⟨x, s⟩, hp, he⟩ := Finset.mem_image.mp h
    have hs : s = t := congrArg Prod.snd he
    subst s
    exact ⟨x, hp, congrArg Prod.fst he⟩
  · rintro ⟨x, hx, he⟩
    exact Finset.mem_image.mpr ⟨(x, t), hx, Prod.ext he rfl⟩

private theorem witness_ordered (P : Finset Point) (d tau : Int)
    (hP : Satisfied (P : Set Point)) (hpivot : (d, tau) ∈ P)
    {a t b u : Int} (ha : (a, t) ∈ clipAfter d tau P)
    (hb : (b, u) ∈ clipAfter d tau P) (hab : a ≠ b) (htu : t < u) :
    ∃ p ∈ (clipAfter d tau P : Set Point),
      InRectangle (min a b) t (max a b) u p ∧
      p ≠ (a, t) ∧ p ≠ (b, u) := by
  obtain ⟨x, hx, hxa⟩ := mem_clipAfter.mp ha
  obtain ⟨y, hy, hyb⟩ := mem_clipAfter.mp hb
  by_cases hu : u ≤ tau
  · have ht : ¬ tau < t := by omega
    have hu' : ¬ tau < u := by omega
    simp only [if_neg ht] at hxa
    simp only [if_neg hu'] at hyb
    subst x
    subst y
    obtain ⟨p, hp, hrect, hpa, hpb⟩ :=
      witness_time_ordered hP hx hy hab htu
    have hpu : p.2 ≤ u := by simpa [max_eq_right (le_of_lt htu)] using hrect.2.2.2
    refine ⟨p, Finset.mem_image.mpr ⟨p, hp, ?_⟩, hrect, hpa, hpb⟩
    simp [show ¬ tau < p.2 by omega]
  have hut : tau < u := by omega
  simp only [if_pos hut] at hyb
  by_cases ht : tau < t
  · simp only [if_pos ht] at hxa
    let Q := mapColumns (fun z => min z d) P
    have hQ : Satisfied (Q : Set Point) :=
      satisfied_mapColumns P _ (fun _ _ h => min_le_min_right _ h) hP
    have haQ : (a, t) ∈ (Q : Set Point) :=
      Finset.mem_image.mpr ⟨(x, t), hx, Prod.ext hxa rfl⟩
    have hbQ : (b, u) ∈ (Q : Set Point) :=
      Finset.mem_image.mpr ⟨(y, u), hy, Prod.ext hyb rfl⟩
    obtain ⟨p, hp, hrect, hpa, hpb⟩ :=
      witness_time_ordered hQ haQ hbQ hab htu
    have htp : t ≤ p.2 := by simpa [min_eq_left (le_of_lt htu)] using hrect.2.2.1
    obtain ⟨z, hz, hzp⟩ := Finset.mem_image.mp hp
    have htime := congrArg (fun w : Point => w.2) hzp
    change z.2 = p.2 at htime
    refine ⟨p, Finset.mem_image.mpr ⟨z, hz, ?_⟩, hrect, hpa, hpb⟩
    simpa [show tau < z.2 by omega] using hzp
  · simp only [if_neg ht] at hxa
    subst x
    have hbd : b ≤ d := by rw [← hyb]; exact min_le_right _ _
    have hpivot' : (d, tau) ∈ clipAfter d tau P :=
      mem_clipAfter.mpr ⟨d, hpivot, by simp⟩
    by_cases had : d < a
    · refine ⟨(d, tau), hpivot', ?_, ?_, ?_⟩
      · simp only [InRectangle]
        constructor
        · omega
        constructor
        · omega
        constructor <;> omega
      · intro he; have := congrArg Prod.fst he; omega
      · intro he; have := congrArg Prod.snd he; omega
    by_cases hbe : b = d
    · refine ⟨(d, tau), hpivot', ?_, ?_, ?_⟩
      · simp only [InRectangle]
        constructor
        · omega
        constructor
        · omega
        constructor <;> omega
      · intro he; have := congrArg Prod.fst he; omega
      · intro he; have := congrArg Prod.snd he; omega
    · have hyy : y = b := by omega
      subst y
      obtain ⟨p, hp, hrect, hpa, hpb⟩ :=
        witness_time_ordered hP hx hy hab htu
      have hpd : p.1 ≤ d := by have := hrect.2.1; omega
      refine ⟨p, Finset.mem_image.mpr ⟨p, hp, ?_⟩, hrect, hpa, hpb⟩
      simp [min_eq_left hpd]

theorem satisfied_clipAfter (P : Finset Point) (d tau : Int)
    (hP : Satisfied (P : Set Point)) (hpivot : (d, tau) ∈ P) :
    Satisfied (clipAfter d tau P : Set Point) := by
  intro a t b u ha hb hab htu
  rcases lt_or_gt_of_ne htu with h | h
  · simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] using
      witness_ordered P d tau hP hpivot ha hb (ne_of_lt hab) h
  · obtain ⟨p, hp, hr', hpb, hpa⟩ :=
      witness_ordered P d tau hP hpivot hb ha (ne_of_gt hab) h
    refine ⟨p, hp, ?_, hpa, hpb⟩
    simpa [InRectangle, min_eq_right (le_of_lt hab),
      max_eq_left (le_of_lt hab), min_comm t u, max_comm t u] using hr'

theorem card_clipAfter (P : Finset Point) (d tau : Int) :
    (clipAfter d tau P).card ≤ P.card := Finset.card_image_le

theorem past_survives (P : Finset Point) (d tau : Int) {x t : Int}
    (h : (x, t) ∈ P) (ht : t ≤ tau) : (x, t) ∈ clipAfter d tau P :=
  mem_clipAfter.mpr ⟨x, h, by simp [show ¬ tau < t by omega]⟩

theorem below_survives (P : Finset Point) (d tau : Int) {x t : Int}
    (h : (x, t) ∈ P) (hx : x ≤ d) : (x, t) ∈ clipAfter d tau P :=
  mem_clipAfter.mpr ⟨x, h, by simp [min_eq_left hx]⟩

end TangoSquared.ArboralCapSplice
