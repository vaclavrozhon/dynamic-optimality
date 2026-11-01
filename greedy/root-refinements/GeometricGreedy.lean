import SurfaceOwners

/-!
The exact greedy row in the last-height representation of geometric BSTs.
For a new-row point and a previous top point, a rectangle is satisfied by
another old point at least as high, another new-row point strictly between
the columns, or the new point above the old column. Older non-top points
are already witnessed by their column's top point. Thus this row condition
is the direct finite-height rectangle condition, with the new row above
all old heights.

The neighborhood row is the inclusion-least satisfying augmentation of a
requested point. This proof does not use the canonical refinement.
-/

namespace GreedyMerge.Geometry

open Surface

def Between (left right point : ℕ) : Prop :=
  min left right ≤ point ∧ point ≤ max left right

/-- Visibility through strict-height neighborhoods is transitive. -/
theorem neighborhood_trans {height : ℕ → ℤ} {n first middle last : ℕ}
    (firstVisible : Neighborhood height n middle first)
    (middleVisible : Neighborhood height n last middle) :
    Neighborhood height n last first := by
  by_cases same : last = middle
  · simpa only [same] using firstVisible
  have middleLower : height middle < height last :=
    middleVisible.2.2 middle (by omega) (by omega) (Ne.symm same)
  refine ⟨middleVisible.1, firstVisible.2.1, ?_⟩
  intro point lo hi different
  by_cases inner : min last middle ≤ point ∧ point ≤ max last middle
  · exact middleVisible.2.2 point inner.1 inner.2 different
  · have outer : min middle first ≤ point ∧ point ≤ max middle first := by omega
    by_cases atMiddle : point = middle
    · simpa only [atMiddle] using middleLower
    · exact lt_trans (firstVisible.2.2 point outer.1 outer.2 atMiddle) middleLower

/-- Every top-point rectangle whose new endpoint is in the row contains
another point. Same-column pairs are already satisfied. -/
def RowSatisfies (height : ℕ → ℤ) (n : ℕ) (row : Finset ℕ) : Prop :=
  (∀ start ∈ row, start < n) ∧
  ∀ start ∈ row, ∀ old, old < n → old ≠ start →
    old ∈ row ∨
    (∃ blocker, Between start old blocker ∧ blocker ≠ old ∧ height old ≤ height blocker) ∨
    (∃ point ∈ row, Between start old point ∧ point ≠ start ∧ point ≠ old)

noncomputable def GreedyRow (height : ℕ → ℤ) (n access : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun key => Neighborhood height n key access

@[simp] theorem mem_greedyRow {height : ℕ → ℤ} {n access key : ℕ} :
    key ∈ GreedyRow height n access ↔ Neighborhood height n key access := by
  classical
  simp only [GreedyRow, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem access_mem_greedyRow (height : ℕ → ℤ) {n access : ℕ} (bound : access < n) :
    access ∈ GreedyRow height n access :=
  mem_greedyRow.mpr (neighborhood_self height bound)

theorem greedyRow_satisfies (height : ℕ → ℤ) {n access : ℕ} :
    RowSatisfies height n (GreedyRow height n access) := by
  classical
  refine ⟨fun start member => (mem_greedyRow.mp member).1, ?_⟩
  intro start member old oldBound different
  have startVisible := mem_greedyRow.mp member
  by_cases visible : Neighborhood height n old start
  · exact Or.inl (mem_greedyRow.mpr (neighborhood_trans startVisible visible))
  · have blocker : ∃ point, min old start ≤ point ∧ point ≤ max old start ∧
        point ≠ old ∧ height old ≤ height point := by
      unfold Neighborhood at visible
      push Not at visible
      have bad := visible oldBound startVisible.1
      obtain ⟨point, lo, hi, ne, badHeight⟩ := bad
      exact ⟨point, lo, hi, ne, badHeight⟩
    obtain ⟨point, lo, hi, ne, badHeight⟩ := blocker
    exact Or.inr (Or.inl ⟨point, ⟨by omega, by omega⟩, ne, badHeight⟩)

/-- Any satisfying row containing the request must contain every visible
column. The nearest row point to a missing visible column would otherwise
form an empty rectangle with that column's previous top point. -/
theorem greedyRow_subset_of_satisfies {height : ℕ → ℤ} {n access : ℕ}
    {row : Finset ℕ} (accessMember : access ∈ row)
    (satisfies : RowSatisfies height n row) :
    GreedyRow height n access ⊆ row := by
  classical
  intro old member
  have visible := mem_greedyRow.mp member
  by_contra missing
  let candidates := row.filter fun point => Between access old point
  have nonempty : candidates.Nonempty := by
    refine ⟨access, Finset.mem_filter.mpr ⟨accessMember, ?_⟩⟩
    constructor <;> omega
  obtain ⟨near, nearMember, nearest⟩ :=
    Finset.exists_min_image candidates (fun point => Distance point old) nonempty
  have nearSpec := Finset.mem_filter.mp nearMember
  have nearBounds : Between access old near := nearSpec.2
  have nearDifferent : old ≠ near := by
    intro equal
    exact missing (equal ▸ nearSpec.1)
  rcases satisfies.2 near nearSpec.1 old visible.1 nearDifferent with already | blocked | filled
  · exact missing already
  · obtain ⟨blocker, blockBounds, notOld, blockHeight⟩ := blocked
    have lo : min old access ≤ blocker := by
      dsimp [Between] at nearBounds blockBounds
      omega
    have hi : blocker ≤ max old access := by
      dsimp [Between] at nearBounds blockBounds
      omega
    have lower := visible.2.2 blocker lo hi notOld
    omega
  · obtain ⟨point, pointMember, pointBounds, notNear, notOld⟩ := filled
    have inCandidates : point ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨pointMember, ?_⟩
      dsimp [Between] at nearBounds pointBounds ⊢
      omega
    have closer := distance_strict_between pointBounds.1 pointBounds.2 notNear
    have minimal := nearest point inCandidates
    omega

/-- Exact unique least augmentation, not merely a feasible greedy row. -/
theorem greedyRow_is_least (height : ℕ → ℤ) {n access : ℕ} (bound : access < n) :
    access ∈ GreedyRow height n access ∧
    RowSatisfies height n (GreedyRow height n access) ∧
    ∀ row, access ∈ row → RowSatisfies height n row → GreedyRow height n access ⊆ row := by
  exact ⟨access_mem_greedyRow height bound, greedyRow_satisfies height,
    fun _ member satisfies => greedyRow_subset_of_satisfies member satisfies⟩

end GreedyMerge.Geometry

#print axioms GreedyMerge.Geometry.greedyRow_is_least
