import DynamicOptimality.ReferenceClosure.Cut

/-!+# A row witnesses every crossing of a key cut

In a finite arborally satisfied set, points on both sides of a key cut
force either a point on the cut or a row containing points on both sides.
This is the finite geometric fact used for closure over time intervals.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

section Ordered

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem ConvexKeys.between {keys : Set α} (convex : ConvexKeys keys)
    {a b c : α} (ha : a ∈ keys) (hb : b ∈ keys)
    (lower : min a b ≤ c) (upper : c ≤ max a b) : c ∈ keys := by
  by_cases le : a ≤ b
  · exact convex a ha b hb c (by simpa [min_eq_left le] using lower)
      (by simpa [max_eq_right le] using upper)
  · exact convex b hb a ha c (by simpa [min_eq_right (le_of_not_ge le)] using lower)
      (by simpa [max_eq_left (le_of_not_ge le)] using upper)

open scoped Classical in
theorem Satisfied.restrict {points : Finset (α × β)} (satisfied : Satisfied points)
    {keys : Set α} {times : Set β} (keyConvex : ConvexKeys keys) (timeConvex : ConvexKeys times) :
    Satisfied (points.filter fun p => p.1 ∈ keys ∧ p.2 ∈ times) := by
  classical
  intro p hp q hq hk ht
  obtain ⟨hp, hpk, hpt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqk, hqt⟩ := Finset.mem_filter.mp hq
  obtain ⟨r, hr, nrp, nrq, rkl, rku, rtl, rtu⟩ := satisfied p hp q hq hk ht
  exact ⟨r, Finset.mem_filter.mpr ⟨hr, keyConvex.between hpk hqk rkl rku,
    timeConvex.between hpt hqt rtl rtu⟩, nrp, nrq, rkl, rku, rtl, rtu⟩

private theorem crossing_of_time_le {points : Finset (α × β)} (satisfied : Satisfied points)
    {pivot : α} {a b : α × β} (ha : a ∈ points) (hb : b ∈ points)
    (left : a.1 < pivot) (right : pivot < b.1) (timeLe : a.2 ≤ b.2) :
    (∃ p ∈ points, p.1 = pivot) ∨ ∃ time, Straddles points Set.univ pivot time := by
  classical
  let leftPoints := points.filter fun p => p.1 < pivot ∧ a.2 ≤ p.2 ∧ p.2 ≤ b.2
  have haL : a ∈ leftPoints := Finset.mem_filter.mpr ⟨ha, left, le_rfl, timeLe⟩
  obtain ⟨c, hc, latest⟩ := Finset.exists_max_image leftPoints Prod.snd ⟨a, haL⟩
  let lastLeft := leftPoints.filter fun p => p.2 = c.2
  have hcL : c ∈ lastLeft := Finset.mem_filter.mpr ⟨hc, rfl⟩
  obtain ⟨z, hzL, largest⟩ := Finset.exists_max_image lastLeft Prod.fst ⟨c, hcL⟩
  obtain ⟨hzLP, hzc⟩ := Finset.mem_filter.mp hzL
  obtain ⟨hz, zLeft, zAfter, zBefore⟩ := Finset.mem_filter.mp hzLP
  let rightPoints := points.filter fun p => pivot < p.1 ∧ z.2 ≤ p.2 ∧ p.2 ≤ b.2
  have hbR : b ∈ rightPoints := Finset.mem_filter.mpr ⟨hb, right, zBefore, le_rfl⟩
  obtain ⟨d, hd, earliest⟩ := Finset.exists_min_image rightPoints Prod.snd ⟨b, hbR⟩
  let firstRight := rightPoints.filter fun p => p.2 = d.2
  have hdR : d ∈ firstRight := Finset.mem_filter.mpr ⟨hd, rfl⟩
  obtain ⟨q, hqR, smallest⟩ := Finset.exists_min_image firstRight Prod.fst ⟨d, hdR⟩
  obtain ⟨hqRP, hqd⟩ := Finset.mem_filter.mp hqR
  obtain ⟨hq, qRight, qAfter, qBefore⟩ := Finset.mem_filter.mp hqRP
  by_cases sameTime : z.2 = q.2
  · exact Or.inr ⟨z.2, z, hz, q, hq, rfl, sameTime.symm,
      Set.mem_univ _, Set.mem_univ _, zLeft, qRight⟩
  · have timeLt : z.2 < q.2 := lt_of_le_of_ne qAfter sameTime
    have keyLt : z.1 < q.1 := zLeft.trans qRight
    obtain ⟨r, hr, nrz, nrq, rkl, rku, rtl, rtu⟩ :=
      satisfied z hz q hq (ne_of_lt keyLt) (ne_of_lt timeLt)
    rw [min_eq_left keyLt.le] at rkl
    rw [max_eq_right keyLt.le] at rku
    rw [min_eq_left timeLt.le] at rtl
    rw [max_eq_right timeLt.le] at rtu
    rcases lt_trichotomy r.1 pivot with before | on | after
    · have hrL : r ∈ leftPoints := Finset.mem_filter.mpr
        ⟨hr, before, zAfter.trans rtl, rtu.trans qBefore⟩
      have timeUpper : r.2 ≤ z.2 := by simpa [hzc] using latest r hrL
      have timeEq : r.2 = z.2 := le_antisymm timeUpper rtl
      have hrLast : r ∈ lastLeft := Finset.mem_filter.mpr ⟨hrL, timeEq.trans hzc⟩
      exact (nrz (Prod.ext (le_antisymm (largest r hrLast) rkl) timeEq)).elim
    · exact Or.inl ⟨r, hr, on⟩
    · have hrR : r ∈ rightPoints := Finset.mem_filter.mpr
        ⟨hr, after, rtl, rtu.trans qBefore⟩
      have timeLower : q.2 ≤ r.2 := by simpa [hqd] using earliest r hrR
      have timeEq : r.2 = q.2 := le_antisymm rtu timeLower
      have hrFirst : r ∈ firstRight := Finset.mem_filter.mpr ⟨hrR, timeEq.trans hqd⟩
      exact (nrq (Prod.ext (le_antisymm rku (smallest r hrFirst)) timeEq)).elim

theorem Satisfied.crossing {points : Finset (α × β)} (satisfied : Satisfied points)
    {pivot : α} {a b : α × β} (ha : a ∈ points) (hb : b ∈ points)
    (left : a.1 < pivot) (right : pivot < b.1) :
    (∃ p ∈ points, p.1 = pivot) ∨ ∃ time, Straddles points Set.univ pivot time := by
  by_cases ordered : a.2 ≤ b.2
  · exact crossing_of_time_le satisfied ha hb left right ordered
  · exact crossing_of_time_le (β := βᵒᵈ) satisfied.timeDual ha hb left right (le_of_not_ge ordered)

end Ordered

end DynamicOptimality.Geometry.ReferenceClosure
