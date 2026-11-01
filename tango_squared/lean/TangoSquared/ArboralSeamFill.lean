import TangoSquared.ArboralDilation
import Mathlib.Data.Int.Interval

/-!
# Filling a vertical seam between actual endpoints

An arborally satisfied history stays satisfied when one fills a vertical
integer segment whose two endpoints already belong to the history. This
is a geometric statement only: it does not identify a physical cut/join
operation or make the two endpoint requests free.
-/

namespace TangoSquared.ArboralSeamFill

open ArboralDilation

def fill (w s e : Int) (P : Set Point) : Set Point :=
  P ∪ {p | p.1 = w ∧ s ≤ p.2 ∧ p.2 ≤ e}

theorem satisfied_fill {P : Set Point} (hP : Satisfied P)
    (w s e : Int) (hs : (w, s) ∈ P) (he : (w, e) ∈ P) :
    Satisfied (fill w s e P) := by
  intro a t b u ha hb hab htu
  have oldWitness (haP : (a, t) ∈ P) (hbP : (b, u) ∈ P) :
      ∃ p ∈ fill w s e P, InRectangle a t b u p ∧
        p ≠ (a, t) ∧ p ≠ (b, u) := by
    obtain ⟨p, hp, hr, hpa, hpb⟩ := hP a t b u haP hbP hab htu
    exact ⟨p, Or.inl hp, hr, hpa, hpb⟩
  rcases ha with ha | ⟨haw, hst, hte⟩
  · rcases hb with hb | ⟨hbw, hsu, hue⟩
    · exact oldWitness ha hb
    · change b = w at hbw
      subst b
      by_cases hst : s ≤ t
      · by_cases hte : t ≤ e
        · refine ⟨(w, t), Or.inr ⟨rfl, hst, hte⟩, ?_, ?_, ?_⟩
          · simp only [InRectangle]; constructor; omega
            constructor; omega
            exact ⟨min_le_left _ _, le_max_left _ _⟩
          · intro h; have := congrArg Prod.fst h; omega
          · intro h; exact htu (congrArg Prod.snd h)
        · by_cases hueq : u = e
          · subst u; exact oldWitness ha he
          · refine ⟨(w, e), Or.inl he, ?_, ?_, ?_⟩
            · simp only [InRectangle]; constructor; omega
              constructor; omega
              constructor <;> omega
            · intro h; have := congrArg Prod.fst h; omega
            · intro h; have := congrArg Prod.snd h; omega
      · by_cases huseq : u = s
        · subst u; exact oldWitness ha hs
        · refine ⟨(w, s), Or.inl hs, ?_, ?_, ?_⟩
          · simp only [InRectangle]; constructor; omega
            constructor; omega
            constructor <;> omega
          · intro h; have := congrArg Prod.fst h; omega
          · intro h; have := congrArg Prod.snd h; omega
  · change a = w at haw
    subst a
    rcases hb with hb | ⟨hbw, _, _⟩
    · by_cases hsu : s ≤ u
      · by_cases hue : u ≤ e
        · refine ⟨(w, u), Or.inr ⟨rfl, hsu, hue⟩, ?_, ?_, ?_⟩
          · simp only [InRectangle]; constructor; omega
            constructor; omega
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · intro h; exact htu (congrArg Prod.snd h).symm
          · intro h; have := congrArg Prod.fst h; omega
        · by_cases hteq : t = e
          · subst t; exact oldWitness he hb
          · refine ⟨(w, e), Or.inl he, ?_, ?_, ?_⟩
            · simp only [InRectangle]; constructor; omega
              constructor; omega
              constructor <;> omega
            · intro h; have := congrArg Prod.snd h; omega
            · intro h; have := congrArg Prod.fst h; omega
      · by_cases htseq : t = s
        · subst t; exact oldWitness hs hb
        · refine ⟨(w, s), Or.inl hs, ?_, ?_, ?_⟩
          · simp only [InRectangle]; constructor; omega
            constructor; omega
            constructor <;> omega
          · intro h; have := congrArg Prod.snd h; omega
          · intro h; have := congrArg Prod.fst h; omega
    · change b = w at hbw
      omega

def finiteFill (w s e : Int) (P : Finset Point) : Finset Point :=
  P ∪ (Finset.Icc s e).image (fun t => (w, t))

theorem finiteFill_coe (w s e : Int) (P : Finset Point) :
    (finiteFill w s e P : Set Point) = fill w s e (P : Set Point) := by
  ext p
  simp only [finiteFill, Finset.mem_coe, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc, fill, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (hp | ⟨t, ht, htp⟩)
    · exact Or.inl hp
    · right
      subst p
      exact ⟨rfl, ht⟩
  · rintro (hp | ⟨hpw, hsp, hpe⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨p.2, ⟨hsp, hpe⟩, Prod.ext hpw.symm rfl⟩

theorem satisfied_finiteFill (w s e : Int) (P : Finset Point)
    (hP : Satisfied (P : Set Point))
    (hs : (w, s) ∈ P) (he : (w, e) ∈ P) :
    Satisfied (finiteFill w s e P : Set Point) := by
  rw [finiteFill_coe]
  exact satisfied_fill hP w s e hs he

theorem card_finiteFill (w s e : Int) (P : Finset Point) :
    (finiteFill w s e P).card ≤ P.card + (e + 1 - s).toNat := by
  calc
    (finiteFill w s e P).card ≤
        P.card + ((Finset.Icc s e).image (fun t => (w, t))).card :=
      Finset.card_union_le _ _
    _ ≤ P.card + (Finset.Icc s e).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = P.card + (e + 1 - s).toNat := by rw [Int.card_Icc]

theorem original_survives (w s e : Int) (P : Finset Point) {p : Point}
    (hp : p ∈ P) : p ∈ finiteFill w s e P :=
  Finset.mem_union_left _ hp

end TangoSquared.ArboralSeamFill
