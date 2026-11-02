import DynamicOptimality.GeometricModel
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Order

/-!+# Filling a reference cut in every row

The auxiliary ordered-coordinate formulation permits reflection of either
axis. Its specialization to natural keys and integer times is precisely
`Geometry.ArborallySatisfied`, not a different geometric cost model.

A cut at `pivot` inside a convex key interval adds the pivot to exactly
those rows that already contain keys on both sides inside that interval.
The principal theorem proves that this operation preserves satisfaction.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

section Ordered

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

def Satisfied (points : Finset (α × β)) : Prop :=
  ∀ p ∈ points, ∀ q ∈ points, p.1 ≠ q.1 → p.2 ≠ q.2 →
    ∃ r ∈ points, r ≠ p ∧ r ≠ q ∧
      min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 ∧
      min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2

def ConvexKeys (keys : Set α) : Prop :=
  ∀ a ∈ keys, ∀ b ∈ keys, ∀ c, a ≤ c → c ≤ b → c ∈ keys

def Straddles (points : Finset (α × β)) (keys : Set α) (pivot : α) (time : β) : Prop :=
  ∃ a ∈ points, ∃ b ∈ points,
    a.2 = time ∧ b.2 = time ∧ a.1 ∈ keys ∧ b.1 ∈ keys ∧ a.1 < pivot ∧ pivot < b.1

def CutExtension (points extended : Finset (α × β)) (keys : Set α) (pivot : α) : Prop :=
  ∀ p, p ∈ extended ↔ p ∈ points ∨ p.1 = pivot ∧ Straddles points keys pivot p.2

theorem Satisfied.keyDual {points : Finset (α × β)} (h : Satisfied points) :
    @Satisfied αᵒᵈ β _ _ points := by
  intro p hp q hq hk ht
  obtain ⟨r, hr, hnep, hneq, hk₁, hk₂, ht₁, ht₂⟩ := h p hp q hq hk ht
  exact ⟨r, hr, hnep, hneq, hk₂, hk₁, ht₁, ht₂⟩

theorem Satisfied.timeDual {points : Finset (α × β)} (h : Satisfied points) :
    @Satisfied α βᵒᵈ _ _ points := by
  intro p hp q hq hk ht
  obtain ⟨r, hr, hnep, hneq, hk₁, hk₂, ht₁, ht₂⟩ := h p hp q hq hk ht
  exact ⟨r, hr, hnep, hneq, hk₁, hk₂, ht₂, ht₁⟩

theorem ConvexKeys.keyDual {keys : Set α} (h : ConvexKeys keys) :
    @ConvexKeys αᵒᵈ _ keys := by
  intro a ha b hb c hc₁ hc₂
  exact h b hb a ha c hc₂ hc₁

omit [LinearOrder β] in
theorem straddles_keyDual {points : Finset (α × β)} {keys : Set α} {pivot : α} {time : β} :
    Straddles (α := αᵒᵈ) points keys pivot time ↔ Straddles points keys pivot time := by
  constructor <;>
    rintro ⟨a, ha, b, hb, hat, hbt, hak, hbk, hal, hbr⟩
  · exact ⟨b, hb, a, ha, hbt, hat, hbk, hak, hbr, hal⟩
  · exact ⟨b, hb, a, ha, hbt, hat, hbk, hak, hbr, hal⟩

omit [LinearOrder β] in
theorem CutExtension.keyDual {points extended : Finset (α × β)} {keys : Set α} {pivot}
    (h : CutExtension points extended keys pivot) :
    CutExtension (α := αᵒᵈ) points extended keys pivot := by
  intro p
  exact (h p).trans (or_congr Iff.rfl
    (and_congr Iff.rfl (straddles_keyDual (α := α) (β := β)).symm))

omit [LinearOrder β] in
theorem CutExtension.timeDual {points extended : Finset (α × β)} {keys : Set α} {pivot}
    (h : CutExtension points extended keys pivot) :
    CutExtension (β := βᵒᵈ) points extended keys pivot := h

/-- The only substantive rectangle argument: the new corner is at the
lower left. The other three orientations follow by reflecting coordinates. -/
private theorem fresh_corner_witness {points extended : Finset (α × β)}
    {keys : Set α} {pivot : α} (convex : ConvexKeys keys)
    (extension : CutExtension points extended keys pivot) (satisfied : Satisfied points)
    {p q : α × β} (hp : p ∈ extended) (fresh : p ∉ points) (hq : q ∈ extended)
    (horizontal : p.1 < q.1) (vertical : p.2 < q.2) :
    ∃ r ∈ extended, r ≠ p ∧ r ≠ q ∧
      min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 ∧
      min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2 := by
  classical
  have hpivot : p.1 = pivot := ((extension p).mp hp).resolve_left fresh |>.1
  obtain ⟨a, ha, b, hb, hat, hbt, hak, hbk, hal, hbr⟩ :=
    ((extension p).mp hp).resolve_left fresh |>.2
  have qold : q ∈ points := by
    rcases (extension q).mp hq with old | ⟨eq, _⟩
    · exact old
    · exact (ne_of_lt horizontal (hpivot.trans eq.symm)).elim
  by_contra noWitness
  have empty : ∀ r ∈ extended, p.1 ≤ r.1 → r.1 ≤ q.1 →
      p.2 ≤ r.2 → r.2 ≤ q.2 → r = p ∨ r = q := by
    intro r hr h₁ h₂ h₃ h₄
    by_contra neither
    have nrp : r ≠ p := fun eq => neither (Or.inl eq)
    have nrq : r ≠ q := fun eq => neither (Or.inr eq)
    exact noWitness ⟨r, hr, nrp, nrq,
      by simpa [min_eq_left horizontal.le] using h₁,
      by simpa [max_eq_right horizontal.le] using h₂,
      by simpa [min_eq_left vertical.le] using h₃,
      by simpa [max_eq_right vertical.le] using h₄⟩
  have oldExtended : ∀ r ∈ points, r ∈ extended :=
    fun r hr => (extension r).mpr (Or.inl hr)
  have byond : q.1 < b.1 := by
    by_contra h
    have inBox := empty b (oldExtended b hb) (by simpa [hpivot] using hbr.le)
      (le_of_not_gt h) (by simp [hbt]) (by simpa [hbt] using vertical.le)
    rcases inBox with eq | eq
    · exact (fresh (eq ▸ hb)).elim
    · have := congrArg Prod.snd eq
      exact (ne_of_lt vertical (hbt.symm.trans this)).elim
  have pivotKey : pivot ∈ keys := convex a.1 hak b.1 hbk pivot hal.le hbr.le
  have qKey : q.1 ∈ keys :=
    convex pivot pivotKey b.1 hbk q.1 (by simpa [hpivot] using horizontal.le) byond.le
  let candidates := points.filter fun r => r.1 ∈ keys ∧ r.1 < pivot ∧
    p.2 ≤ r.2 ∧ r.2 ≤ q.2
  have haC : a ∈ candidates := by
    simp only [candidates, Finset.mem_filter]
    exact ⟨ha, hak, hal, by simp [hat], by simpa [hat] using vertical.le⟩
  obtain ⟨c, hc, latest⟩ := Finset.exists_max_image candidates Prod.snd ⟨a, haC⟩
  let lastRow := candidates.filter fun r => r.2 = c.2
  have hcR : c ∈ lastRow := by simp [lastRow, hc]
  obtain ⟨z, hzR, rightmost⟩ := Finset.exists_max_image lastRow Prod.fst ⟨c, hcR⟩
  obtain ⟨hzC, hzc⟩ := Finset.mem_filter.mp hzR
  obtain ⟨hz, hzKey, hzLeft, hzLow, hzHigh⟩ := Finset.mem_filter.mp hzC
  have zltq : z.1 < q.1 := hzLeft.trans (by simpa [hpivot] using horizontal)
  have ztime : z.2 < q.2 := by
    by_contra h
    have eq : z.2 = q.2 := le_antisymm hzHigh (le_of_not_gt h)
    have added : (pivot, q.2) ∈ extended := (extension _).mpr (Or.inr ⟨rfl,
      z, hz, q, qold, eq, rfl, hzKey, qKey, hzLeft,
      by simpa [hpivot] using horizontal⟩)
    rcases empty (pivot, q.2) added (by simp [hpivot])
      (by simpa [hpivot] using horizontal.le) vertical.le le_rfl with eq' | eq'
    · have := congrArg Prod.snd eq'
      exact (ne_of_lt vertical this.symm).elim
    · have := congrArg Prod.fst eq'
      exact (ne_of_lt horizontal (hpivot.trans this)).elim
  obtain ⟨r, hr, nrz, nrq, hrLeft, hrRight, hrLow, hrHigh⟩ :=
    satisfied z hz q qold (ne_of_lt zltq) (ne_of_lt ztime)
  rw [min_eq_left zltq.le] at hrLeft
  rw [max_eq_right zltq.le] at hrRight
  rw [min_eq_left ztime.le] at hrLow
  rw [max_eq_right ztime.le] at hrHigh
  by_cases before : r.1 < pivot
  · have hrKey := convex z.1 hzKey q.1 qKey r.1 hrLeft hrRight
    have hrC : r ∈ candidates := Finset.mem_filter.mpr
      ⟨hr, hrKey, before, hzLow.trans hrLow, hrHigh⟩
    have timeLe : r.2 ≤ z.2 := by simpa [hzc] using latest r hrC
    have timeEq : r.2 = z.2 := le_antisymm timeLe hrLow
    have hrR : r ∈ lastRow := Finset.mem_filter.mpr ⟨hrC, timeEq.trans hzc⟩
    have keyEq : r.1 = z.1 := le_antisymm (rightmost r hrR) hrLeft
    exact nrz (Prod.ext keyEq timeEq)
  · rcases empty r (oldExtended r hr) (by simpa [hpivot] using le_of_not_gt before)
      hrRight (hzLow.trans hrLow) hrHigh with eq | eq
    · exact fresh (eq ▸ hr)
    · exact nrq eq

theorem CutExtension.satisfied {points extended : Finset (α × β)}
    {keys : Set α} {pivot : α} (extension : CutExtension points extended keys pivot)
    (convex : ConvexKeys keys) (satisfied : Satisfied points) : Satisfied extended := by
  have freshWitness : ∀ p ∈ extended, p ∉ points → ∀ q ∈ extended,
      p.1 ≠ q.1 → p.2 ≠ q.2 →
      ∃ r ∈ extended, r ≠ p ∧ r ≠ q ∧
        min p.1 q.1 ≤ r.1 ∧ r.1 ≤ max p.1 q.1 ∧
        min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2 := by
    intro p hp fresh q hq hk ht
    rcases lt_or_gt_of_ne hk with hk | hk <;> rcases lt_or_gt_of_ne ht with ht | ht
    · exact fresh_corner_witness convex extension satisfied hp fresh hq hk ht
    · obtain ⟨r, hr, np, nq, k₁, k₂, t₁, t₂⟩ :=
        fresh_corner_witness (β := βᵒᵈ) convex extension.timeDual satisfied.timeDual
          hp fresh hq hk ht
      exact ⟨r, hr, np, nq, k₁, k₂, t₂, t₁⟩
    · obtain ⟨r, hr, np, nq, k₁, k₂, t₁, t₂⟩ :=
        fresh_corner_witness (α := αᵒᵈ) convex.keyDual extension.keyDual satisfied.keyDual
          hp fresh hq hk ht
      exact ⟨r, hr, np, nq, k₂, k₁, t₁, t₂⟩
    · obtain ⟨r, hr, np, nq, k₁, k₂, t₁, t₂⟩ :=
        fresh_corner_witness (α := αᵒᵈ) (β := βᵒᵈ) convex.keyDual
          extension.keyDual.timeDual satisfied.keyDual.timeDual hp fresh hq hk ht
      exact ⟨r, hr, np, nq, k₂, k₁, t₂, t₁⟩
  intro p hp q hq hk ht
  by_cases oldP : p ∈ points
  · by_cases oldQ : q ∈ points
    · obtain ⟨r, hr, rest⟩ := satisfied p oldP q oldQ hk ht
      exact ⟨r, (extension r).mpr (Or.inl hr), rest⟩
    · obtain ⟨r, hr, np, nq, k₁, k₂, t₁, t₂⟩ :=
        freshWitness q hq oldQ p hp hk.symm ht.symm
      exact ⟨r, hr, nq, np, by simpa [min_comm] using k₁,
        by simpa [max_comm] using k₂, by simpa [min_comm] using t₁,
        by simpa [max_comm] using t₂⟩
  · exact freshWitness p hp oldP q hq hk ht

/-- The finite realization of the cut extension. -/
noncomputable def fillCut (points : Finset (α × β)) (keys : Set α) (pivot : α) :
    Finset (α × β) := by
  classical
  exact points ∪
    (points.filter fun p => Straddles points keys pivot p.2).image (fun p => (pivot, p.2))

theorem fillCut_extension (points : Finset (α × β)) (keys : Set α) (pivot : α) :
    CutExtension points (fillCut points keys pivot) keys pivot := by
  classical
  intro p
  simp only [fillCut, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (old | ⟨a, ⟨_, straddles⟩, eq⟩)
    · exact Or.inl old
    · have hk := congrArg Prod.fst eq
      have ht := congrArg Prod.snd eq
      exact Or.inr ⟨hk.symm, ht ▸ straddles⟩
  · rintro (old | ⟨eq, straddles⟩)
    · exact Or.inl old
    · obtain ⟨a, ha, b, hb, hat, hbt, hak, hbk, hal, hbr⟩ := straddles
      refine Or.inr ⟨a, ⟨ha, ?_⟩, Prod.ext eq.symm hat⟩
      exact ⟨a, ha, b, hb, rfl, hbt.trans hat.symm, hak, hbk, hal, hbr⟩

theorem fillCut_satisfied {points : Finset (α × β)} {keys : Set α} {pivot : α}
    (convex : ConvexKeys keys) (satisfied : Satisfied points) :
    Satisfied (fillCut points keys pivot) :=
  (fillCut_extension points keys pivot).satisfied convex satisfied

end Ordered

theorem satisfied_iff (points : Finset Point) :
    Satisfied points ↔ ArborallySatisfied points := by
  simp only [Satisfied, ArborallySatisfied, GreedyMerge.Geometry.Between, and_assoc]

end DynamicOptimality.Geometry.ReferenceClosure
