import TangoSquared.ArboralQuotient
import Mathlib.Data.Int.Interval

/-!
# Arboral certificates with an increasing right cap

The cap may grow over time, provided its old value is genuinely touched
on the row of every increase. This is a geometric state-transport theorem.
It does not implement insertion of new physical BST keys.
-/

namespace TangoSquared.ArboralGrowingCap

open ArboralDilation ArboralQuotient

def capColumns (r : Int → Int) (P : Finset Point) : Finset Point :=
  P.image (fun p => (min p.1 (r p.2), p.2))

theorem mem_capColumns {r : Int → Int} {P : Finset Point} {a t : Int} :
    (a, t) ∈ capColumns r P ↔ ∃ x, (x, t) ∈ P ∧ min x (r t) = a := by
  constructor
  · intro h
    obtain ⟨⟨x, s⟩, hp, he⟩ := Finset.mem_image.mp h
    have hs : s = t := congrArg Prod.snd he
    subst s
    exact ⟨x, hp, congrArg Prod.fst he⟩
  · rintro ⟨x, hx, he⟩
    exact Finset.mem_image.mpr ⟨(x, t), hx, Prod.ext he rfl⟩

/-- A temporal orientation of the rectangle-witness property. -/
theorem witness_time_ordered {P : Set Point} (hP : Satisfied P)
    {a t b u : Int} (ha : (a, t) ∈ P) (hb : (b, u) ∈ P)
    (hab : a ≠ b) (htu : t < u) :
    ∃ p ∈ P, InRectangle (min a b) t (max a b) u p ∧
      p ≠ (a, t) ∧ p ≠ (b, u) := by
  by_cases h : a < b
  · simpa [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)] using
      hP a t b u ha hb h (ne_of_lt htu)
  · have h' : b < a := by omega
    obtain ⟨p, hp, hr, hpb, hpa⟩ := hP b u a t hb ha h' (ne_of_gt htu)
    refine ⟨p, hp, ?_, hpa, hpb⟩
    simpa [InRectangle, min_eq_right (le_of_lt h'),
      max_eq_left (le_of_lt h'), min_comm u t, max_comm u t] using hr

/-- Between two different cap values, the first old boundary is touched. -/
def CrossingWitness (P : Finset Point) (r : Int → Int) : Prop :=
  ∀ t u, t < u → r t < r u →
    ∃ v, t < v ∧ v ≤ u ∧ (r t, v) ∈ capColumns r P

private theorem cap_witness_time_ordered (P : Finset Point) (r : Int → Int)
    (hr : Monotone r) (hP : Satisfied (P : Set Point))
    (hc : CrossingWitness P r)
    {a t b u : Int} (ha : (a, t) ∈ capColumns r P)
    (hb : (b, u) ∈ capColumns r P) (hab : a ≠ b) (htu : t < u) :
    ∃ p ∈ (capColumns r P : Set Point),
      InRectangle (min a b) t (max a b) u p ∧
      p ≠ (a, t) ∧ p ≠ (b, u) := by
  obtain ⟨x, hx, hxa⟩ := mem_capColumns.mp ha
  obtain ⟨y, hy, hyb⟩ := mem_capColumns.mp hb
  have hcap := hr (le_of_lt htu)
  have hac : a ≤ r t := by rw [← hxa]; exact min_le_right _ _
  by_cases he : r t = r u
  · let Q := mapColumns (fun z => min z (r t)) P
    have hQ : Satisfied (Q : Set Point) :=
      satisfied_mapColumns P _ (fun _ _ h => min_le_min_right _ h) hP
    have haQ : (a, t) ∈ (Q : Set Point) :=
      Finset.mem_image.mpr ⟨(x, t), hx, Prod.ext hxa rfl⟩
    have hbQ : (b, u) ∈ (Q : Set Point) :=
      Finset.mem_image.mpr ⟨(y, u), hy, Prod.ext (by simpa [he] using hyb) rfl⟩
    obtain ⟨p, hp, hrect, hpa, hpb⟩ :=
      witness_time_ordered hQ haQ hbQ hab htu
    have htp : t ≤ p.2 := by simpa [min_eq_left (le_of_lt htu)] using hrect.2.2.1
    have hpu : p.2 ≤ u := by simpa [max_eq_right (le_of_lt htu)] using hrect.2.2.2
    have hpcap : r p.2 = r t := by
      have := hr htp
      have := hr hpu
      omega
    obtain ⟨z, hz, hzp⟩ := Finset.mem_image.mp hp
    have htime := congrArg (fun w : Point => w.2) hzp
    change z.2 = p.2 at htime
    refine ⟨p, ?_, hrect, hpa, hpb⟩
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    simpa [htime, hpcap] using hzp
  · have hstrict : r t < r u := by omega
    obtain ⟨v, htv, hvu, hcv⟩ := hc t u htu hstrict
    by_cases hae : a = r t
    · refine ⟨(r t, v), hcv, ?_, ?_, ?_⟩
      · simp only [InRectangle]
        constructor
        · omega
        constructor
        · omega
        constructor <;> omega
      · intro hh; have := congrArg Prod.snd hh; omega
      · intro hh; have := congrArg Prod.fst hh; omega
    have halt : a < r t := by omega
    by_cases hbc : r t < b
    · refine ⟨(r t, v), hcv, ?_, ?_, ?_⟩
      · simp only [InRectangle]
        constructor
        · omega
        constructor
        · omega
        constructor <;> omega
      · intro hh; have := congrArg Prod.fst hh; omega
      · intro hh; have := congrArg Prod.fst hh; omega
    · have hbc' : b ≤ r t := by omega
      have hxx : x = a := by omega
      have hyy : y = b := by omega
      subst x
      subst y
      obtain ⟨p, hp, hrect, hpa, hpb⟩ :=
        witness_time_ordered hP hx hy hab htu
      have htp : t ≤ p.2 := by
        simpa [min_eq_left (le_of_lt htu)] using hrect.2.2.1
      have hpx : p.1 ≤ r t := by
        have := hrect.2.1
        omega
      have hpr : p.1 ≤ r p.2 := le_trans hpx (hr htp)
      refine ⟨p, Finset.mem_image.mpr ⟨p, hp, ?_⟩, hrect, hpa, hpb⟩
      exact Prod.ext (min_eq_left hpr) rfl

theorem satisfied_capColumns_of_crossing (P : Finset Point) (r : Int → Int)
    (hr : Monotone r) (hP : Satisfied (P : Set Point))
    (hc : CrossingWitness P r) :
    Satisfied (capColumns r P : Set Point) := by
  intro a t b u ha hb hab htu
  rcases lt_or_gt_of_ne htu with h | h
  · simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)] using
      cap_witness_time_ordered P r hr hP hc ha hb (ne_of_lt hab) h
  · obtain ⟨p, hp, hr', hpb, hpa⟩ :=
      cap_witness_time_ordered P r hr hP hc hb ha (ne_of_gt hab) h
    refine ⟨p, hp, ?_, hpa, hpb⟩
    simpa [InRectangle, min_eq_right (le_of_lt hab),
      max_eq_left (le_of_lt hab), min_comm t u, max_comm t u] using hr'

theorem card_capColumns (P : Finset Point) (r : Int → Int) :
    (capColumns r P).card ≤ P.card := Finset.card_image_le

/-- A local birth rule: every increase touches the previous actual cap. -/
def OldCapTouched (P : Finset Point) (r : Int → Int) : Prop :=
  ∀ v, r (v - 1) < r v → (r (v - 1), v) ∈ P

theorem crossing_of_oldCapTouched (P : Finset Point) (r : Int → Int)
    (hr : Monotone r) (hb : OldCapTouched P r) : CrossingWitness P r := by
  intro t u htu hcap
  let S := (Finset.Icc (t + 1) u).filter (fun v => r t < r v)
  have hS : S.Nonempty := by
    refine ⟨u, Finset.mem_filter.mpr ⟨?_, hcap⟩⟩
    exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  let v := S.min' hS
  have hv : v ∈ S := Finset.min'_mem S hS
  obtain ⟨hvi, hvbig⟩ := Finset.mem_filter.mp hv
  obtain ⟨htv, hvu⟩ := Finset.mem_Icc.mp hvi
  have hvprev : r (v - 1) = r t := by
    have hge := hr (show t ≤ v - 1 by omega)
    by_contra hne
    have hgt : r t < r (v - 1) := by omega
    by_cases he : v = t + 1
    · have : v - 1 = t := by omega
      simp [this] at hgt
    · have hprev : v - 1 ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hgt⟩
      have hmin : v ≤ v - 1 := Finset.min'_le S (v - 1) hprev
      omega
  have hvjump : r (v - 1) < r v := by omega
  have hp := hb v hvjump
  rw [hvprev] at hp
  refine ⟨v, by omega, hvu, mem_capColumns.mpr ⟨r t, hp, ?_⟩⟩
  exact min_eq_left (le_of_lt hvbig)

/-- The complete finite growing-cap theorem, with a concrete local birth rule. -/
theorem satisfied_capColumns (P : Finset Point) (r : Int → Int)
    (hr : Monotone r) (hP : Satisfied (P : Set Point))
    (hb : OldCapTouched P r) :
    Satisfied (capColumns r P : Set Point) :=
  satisfied_capColumns_of_crossing P r hr hP (crossing_of_oldCapTouched P r hr hb)

theorem query_survives (P : Finset Point) (r : Int → Int) {x t : Int}
    (h : (x, t) ∈ P) (hx : x ≤ r t) : (x, t) ∈ capColumns r P :=
  mem_capColumns.mpr ⟨x, h, min_eq_left hx⟩

/-- Activating the next rank by a genuine request supplies the old cap
through dilation in the fixed virtual alphabet, before time-varying clipping. -/
theorem activated_certificate (P : Finset Point) (r : Int → Int)
    (hr : Monotone r) (hP : Satisfied (P : Set Point))
    (hb : ∀ v, r (v - 1) < r v →
      r v = r (v - 1) + 1 ∧ (r v, v) ∈ P) :
    Satisfied (capColumns r (finiteDilation 1 P) : Set Point) ∧
      (capColumns r (finiteDilation 1 P)).card ≤ 3 * P.card := by
  have hD : (finiteDilation 1 P : Set Point) = dilate 1 (P : Set Point) := by
    ext p
    exact mem_finiteDilation 1 P p
  have hDP : Satisfied (finiteDilation 1 P : Set Point) := by
    rw [hD]
    exact satisfied_dilate hP (by omega)
  have hbirth : OldCapTouched (finiteDilation 1 P) r := by
    intro v hv
    obtain ⟨hstep, hnew⟩ := hb v hv
    rw [mem_finiteDilation]
    exact ⟨r v, hnew, by omega, by omega⟩
  constructor
  · exact satisfied_capColumns _ r hr hDP hbirth
  · have h₁ := card_capColumns (finiteDilation 1 P) r
    have h₂ := finiteDilation_card_le 1 P
    omega

theorem active_neighbor_survives (P : Finset Point) (r : Int → Int)
    {x t a : Int} (hx : (x, t) ∈ P) (hlo : x - 1 ≤ a)
    (hhi : a ≤ x + 1) (ha : a ≤ r t) :
    (a, t) ∈ capColumns r (finiteDilation 1 P) := by
  apply query_survives _ _ _ ha
  rw [mem_finiteDilation]
  exact ⟨x, hx, hlo, hhi⟩

end TangoSquared.ArboralGrowingCap
