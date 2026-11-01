import Splay.Rank.Heavy
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Splay.Rank.Snapshot

/-- All interval minima of intervals containing a fixed external position. -/
noncomputable def coveringMinima {n : ℕ} (snapshot : Snapshot n) (position : External n) : Finset (External n) :=
  Finset.univ.filter fun element => ∃ (lower upper : External n) (nonempty : lower ≤ upper),
    lower ≤ position ∧ position ≤ upper ∧ snapshot.intervalMin lower upper nonempty = element

theorem mem_coveringMinima {n : ℕ} (snapshot : Snapshot n) (position element : External n) :
    element ∈ snapshot.coveringMinima position ↔ ∃ (lower upper : External n) (nonempty : lower ≤ upper),
      lower ≤ position ∧ position ≤ upper ∧ snapshot.intervalMin lower upper nonempty = element := by
  classical
  simp [coveringMinima]

/-- Two overlapping intervals cannot have different minima of equal rank:
both would minimize their union, which is itself an interval. -/
theorem minima_eq_of_rank_eq_of_overlap {n : ℕ} (snapshot : Snapshot n)
    {firstLower firstUpper secondLower secondUpper position : External n}
    (firstNonempty : firstLower ≤ firstUpper) (secondNonempty : secondLower ≤ secondUpper)
    (firstContains : firstLower ≤ position ∧ position ≤ firstUpper)
    (secondContains : secondLower ≤ position ∧ position ≤ secondUpper)
    (sameRank : snapshot.rank (snapshot.intervalMin firstLower firstUpper firstNonempty) =
      snapshot.rank (snapshot.intervalMin secondLower secondUpper secondNonempty)) :
    snapshot.intervalMin firstLower firstUpper firstNonempty = snapshot.intervalMin secondLower secondUpper secondNonempty := by
  let lower := min firstLower secondLower
  let upper := max firstUpper secondUpper
  have nonempty : lower ≤ upper := (min_le_left _ _).trans (firstNonempty.trans (le_max_left _ _))
  have firstMin := snapshot.intervalMin_isMin firstLower firstUpper firstNonempty
  have secondMin := snapshot.intervalMin_isMin secondLower secondUpper secondNonempty
  have rankBound (element : External n) (atLower : lower ≤ element) (atUpper : element ≤ upper) :
      snapshot.rank (snapshot.intervalMin firstLower firstUpper firstNonempty) ≤ snapshot.rank element := by
    by_cases inFirst : firstLower ≤ element ∧ element ≤ firstUpper
    · exact firstMin.2.2 element inFirst.1 inFirst.2
    · have inSecond : secondLower ≤ element ∧ element ≤ secondUpper := by
        have lowerCases := min_le_iff.mp atLower
        have upperCases := le_max_iff.mp atUpper
        rcases firstContains with ⟨firstLow, firstHigh⟩
        rcases secondContains with ⟨secondLow, secondHigh⟩
        rcases lowerCases with low | low <;> rcases upperCases with high | high <;>
          simp only [Fin.le_def] at * <;> omega
      rw [sameRank]
      exact secondMin.2.2 element inSecond.1 inSecond.2
  have firstUnion : IsIntervalMin snapshot.rank lower upper (snapshot.intervalMin firstLower firstUpper firstNonempty) :=
    ⟨(min_le_left _ _).trans firstMin.1, firstMin.2.1.trans (le_max_left _ _), rankBound⟩
  have secondUnion : IsIntervalMin snapshot.rank lower upper (snapshot.intervalMin secondLower secondUpper secondNonempty) :=
    ⟨(min_le_right _ _).trans secondMin.1, secondMin.2.1.trans (le_max_right _ _), by
      intro element atLower atUpper
      rw [← sameRank]
      exact rankBound element atLower atUpper⟩
  exact (snapshot.intervalMin_unique lower upper nonempty firstUnion).trans
    (snapshot.intervalMin_unique lower upper nonempty secondUnion).symm

theorem coveringMinima_rank_le {n : ℕ} (snapshot : Snapshot n) {position element : External n}
    (member : element ∈ snapshot.coveringMinima position) : snapshot.rank element ≤ snapshot.rank position := by
  obtain ⟨lower, upper, nonempty, atLower, atUpper, rfl⟩ := (snapshot.mem_coveringMinima position element).mp member
  exact (snapshot.intervalMin_isMin lower upper nonempty).2.2 position atLower atUpper

theorem coveringMinima_rank_injective {n : ℕ} (snapshot : Snapshot n) (position : External n) :
    Set.InjOn snapshot.rank (snapshot.coveringMinima position) := by
  intro first firstMember second secondMember sameRank
  obtain ⟨fl, fu, fn, flo, fup, rfl⟩ := (snapshot.mem_coveringMinima position first).mp firstMember
  obtain ⟨sl, su, sn, slo, sup, rfl⟩ := (snapshot.mem_coveringMinima position second).mp secondMember
  exact snapshot.minima_eq_of_rank_eq_of_overlap fn sn ⟨flo, fup⟩ ⟨slo, sup⟩ sameRank

/-- At most rank(position)+1 different owners can be minima of intervals
covering this position, independently of the ambient tree height. -/
theorem coveringMinima_card_le {n : ℕ} (snapshot : Snapshot n) (position : External n) :
    (snapshot.coveringMinima position).card ≤ snapshot.rank position + 1 := by
  classical
  have imageCard : ((snapshot.coveringMinima position).image snapshot.rank).card = (snapshot.coveringMinima position).card :=
    Finset.card_image_iff.mpr (snapshot.coveringMinima_rank_injective position)
  have subset : (snapshot.coveringMinima position).image snapshot.rank ⊆ Finset.range (snapshot.rank position + 1) := by
    intro rank member
    obtain ⟨element, inside, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (snapshot.coveringMinima_rank_le inside))
  have bound := Finset.card_le_card subset
  simpa [imageCard] using bound

end Splay.Rank.Snapshot
