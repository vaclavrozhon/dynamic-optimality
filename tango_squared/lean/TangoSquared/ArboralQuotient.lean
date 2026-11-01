import TangoSquared.ArboralDilation
import Mathlib.Data.Finset.Max

/-!
# Finite arboral certificates survive monotone key quotients

The point set is finite because the proof chooses the inwardmost original
point in each endpoint fiber and row. This prevents an original rectangle
witness from collapsing to an endpoint after a noninjective key map.
The result supports fixed convex exit-block maps; changing maps over time
and maps that fold the order are not covered.
-/

namespace TangoSquared.ArboralQuotient

open ArboralDilation

def mapColumns (f : Int → Int) (P : Finset Point) : Finset Point :=
  P.image (fun p => (f p.1, p.2))

theorem satisfied_mapColumns (P : Finset Point) (f : Int → Int)
    (hf : Monotone f) (hP : Satisfied (P : Set Point)) :
    Satisfied (mapColumns f P : Set Point) := by
  intro a t b u ha hb hab htu
  obtain ⟨pa, hpa, heqa⟩ := Finset.mem_image.mp ha
  obtain ⟨pb, hpb, heqb⟩ := Finset.mem_image.mp hb
  have ha₁ : f pa.1 = a := congrArg Prod.fst heqa
  have ha₂ : pa.2 = t := congrArg Prod.snd heqa
  have hb₁ : f pb.1 = b := congrArg Prod.fst heqb
  have hb₂ : pb.2 = u := congrArg Prod.snd heqb
  let A := P.filter (fun p => f p.1 = a ∧ p.2 = t)
  let B := P.filter (fun p => f p.1 = b ∧ p.2 = u)
  have hA : A.Nonempty := ⟨pa, Finset.mem_filter.mpr ⟨hpa, ha₁, ha₂⟩⟩
  have hB : B.Nonempty := ⟨pb, Finset.mem_filter.mpr ⟨hpb, hb₁, hb₂⟩⟩
  obtain ⟨p, hpA, hpmax⟩ := Finset.exists_max_image A Prod.fst hA
  obtain ⟨q, hqB, hqmin⟩ := Finset.exists_min_image B Prod.fst hB
  obtain ⟨hp, hfp, hpt⟩ := Finset.mem_filter.mp hpA
  obtain ⟨hq, hfq, hqu⟩ := Finset.mem_filter.mp hqB
  have hpq : p.1 < q.1 := by
    by_contra h
    have hqp := hf (show q.1 ≤ p.1 by omega)
    rw [hfp, hfq] at hqp
    omega
  have hp' : (p.1, t) ∈ (P : Set Point) := by simpa [← hpt] using hp
  have hq' : (q.1, u) ∈ (P : Set Point) := by simpa [← hqu] using hq
  obtain ⟨z, hz, hrect, hzp, hzq⟩ := hP p.1 t q.1 u hp' hq' hpq htu
  rcases hrect with ⟨hpz, hzq', htz, hzu⟩
  refine ⟨(f z.1, z.2), Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_, ?_, ?_⟩
  · exact ⟨by simpa [hfp] using hf hpz, by simpa [hfq] using hf hzq', htz, hzu⟩
  · intro he
    have hza : f z.1 = a := congrArg Prod.fst he
    have hzt : z.2 = t := congrArg Prod.snd he
    have hzA : z ∈ A := Finset.mem_filter.mpr ⟨hz, hza, hzt⟩
    have hzle := hpmax z hzA
    apply hzp
    exact Prod.ext (by omega) hzt
  · intro he
    have hzb : f z.1 = b := congrArg Prod.fst he
    have hzu' : z.2 = u := congrArg Prod.snd he
    have hzB : z ∈ B := Finset.mem_filter.mpr ⟨hz, hzb, hzu'⟩
    have hzge := hqmin z hzB
    apply hzq
    exact Prod.ext (by omega) hzu'

theorem card_mapColumns (P : Finset Point) (f : Int → Int) :
    (mapColumns f P).card ≤ P.card := Finset.card_image_le

theorem query_survives (P : Finset Point) (f : Int → Int) {x t : Int}
    (h : (x, t) ∈ P) : (f x, t) ∈ mapColumns f P :=
  Finset.mem_image.mpr ⟨(x, t), h, rfl⟩

end TangoSquared.ArboralQuotient
