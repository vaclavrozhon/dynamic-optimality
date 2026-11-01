import GeometricGreedy
import SurfaceUpdate

/-!
Explicit finite historical point-set interpretation of the last-height
row condition. Every new/old non-aligned rectangle is satisfied exactly
when the finite-height row condition holds. Historical old/old rectangles
are unaffected, so an already arborally satisfied past remains satisfied.
-/

namespace GreedyMerge.Geometry

abbrev Point := ℕ × ℤ

def HasSurface (history : Finset Point) (height : ℕ → ℤ) (n : ℕ) : Prop :=
  (∀ point ∈ history, point.1 < n ∧ point.2 ≤ height point.1) ∧
  ∀ key, key < n → (key, height key) ∈ history

def Augment (history : Finset Point) (time : ℤ) (row : Finset ℕ) : Finset Point :=
  history ∪ row.image (fun key => (key, time))

def NewOldWitness (history : Finset Point) (time : ℤ) (row : Finset ℕ)
    (start : ℕ) (old : Point) : Prop :=
  ∃ point ∈ Augment history time row,
    point ≠ (start, time) ∧ point ≠ old ∧
    Between start old.1 point.1 ∧ old.2 ≤ point.2 ∧ point.2 ≤ time

def NewRectanglesSatisfied (history : Finset Point) (n : ℕ)
    (time : ℤ) (row : Finset ℕ) : Prop :=
  (∀ start ∈ row, start < n) ∧
  ∀ start ∈ row, ∀ old ∈ history, old.1 ≠ start →
    NewOldWitness history time row start old

theorem old_mem_augment {history : Finset Point} {time : ℤ} {row : Finset ℕ}
    {point : Point} (member : point ∈ history) : point ∈ Augment history time row :=
  Finset.mem_union_left _ member

theorem new_mem_augment {history : Finset Point} {time : ℤ} {row : Finset ℕ}
    {key : ℕ} (member : key ∈ row) : (key, time) ∈ Augment history time row :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨key, member, rfl⟩)

theorem rectangle_row_necessary {history : Finset Point} {height : ℕ → ℤ}
    {n : ℕ} {time : ℤ} {row : Finset ℕ}
    (surface : HasSurface history height n)
    (satisfied : NewRectanglesSatisfied history n time row) :
    RowSatisfies height n row := by
  refine ⟨satisfied.1, ?_⟩
  intro start startMember old oldBound different
  obtain ⟨point, pointMember, notNew, notOld, between, lo, hi⟩ :=
    satisfied.2 start startMember (old, height old) (surface.2 old oldBound) different
  rcases Finset.mem_union.mp pointMember with historical | new
  · have topBound := surface.1 point historical
    have otherColumn : point.1 ≠ old := by
      intro same
      have upper : point.2 ≤ height old := by simpa only [same] using topBound.2
      have timeEq : point.2 = height old := le_antisymm upper lo
      exact notOld (Prod.ext same timeEq)
    exact Or.inr (Or.inl ⟨point.1, between, otherColumn, le_trans lo topBound.2⟩)
  · obtain ⟨key, keyMember, pointEq⟩ := Finset.mem_image.mp new
    subst point
    by_cases atOld : key = old
    · exact Or.inl (atOld ▸ keyMember)
    · have notStart : key ≠ start := by
        intro same
        exact notNew (Prod.ext same rfl)
      exact Or.inr (Or.inr ⟨key, keyMember, between, notStart, atOld⟩)

theorem rectangle_row_sufficient {history : Finset Point} {height : ℕ → ℤ}
    {n : ℕ} {time : ℤ} {row : Finset ℕ}
    (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time)
    (satisfied : RowSatisfies height n row) :
    NewRectanglesSatisfied history n time row := by
  refine ⟨satisfied.1, ?_⟩
  intro start startMember old oldMember different
  have oldSpec := surface.1 old oldMember
  have topBefore := above old.1 oldSpec.1
  by_cases atTop : old.2 = height old.1
  · rcases satisfied.2 start startMember old.1 oldSpec.1 different with
      column | oldBlock | newBlock
    · refine ⟨(old.1, time), new_mem_augment column, ?_, ?_, ?_, ?_, le_rfl⟩
      · intro equal
        exact different (congrArg Prod.fst equal)
      · intro equal
        have times := congrArg Prod.snd equal
        omega
      · constructor <;> omega
      · omega
    · obtain ⟨blocker, between, notOld, high⟩ := oldBlock
      have blockerBound : blocker < n := by
        have startBound := satisfied.1 start startMember
        dsimp [Between] at between
        omega
      have blockerBefore := above blocker blockerBound
      refine ⟨(blocker, height blocker), old_mem_augment (surface.2 blocker blockerBound),
        ?_, ?_, between, ?_, le_of_lt blockerBefore⟩
      · intro equal
        have times := congrArg Prod.snd equal
        omega
      · intro equal
        exact notOld (congrArg Prod.fst equal)
      · simpa only [atTop] using high
    · obtain ⟨point, pointMember, between, notStart, notOld⟩ := newBlock
      refine ⟨(point, time), new_mem_augment pointMember, ?_, ?_, between, ?_, le_rfl⟩
      · intro equal
        exact notStart (congrArg Prod.fst equal)
      · intro equal
        exact notOld (congrArg Prod.fst equal)
      · omega
  · have strictTop : old.2 < height old.1 := lt_of_le_of_ne oldSpec.2 atTop
    refine ⟨(old.1, height old.1), old_mem_augment (surface.2 old.1 oldSpec.1),
      ?_, ?_, ?_, le_of_lt strictTop, le_of_lt topBefore⟩
    · intro equal
      have times := congrArg Prod.snd equal
      omega
    · intro equal
      have times := congrArg Prod.snd equal
      omega
    · constructor <;> omega

theorem rectangle_row_iff {history : Finset Point} {height : ℕ → ℤ}
    {n : ℕ} {time : ℤ} {row : Finset ℕ}
    (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time) :
    NewRectanglesSatisfied history n time row ↔ RowSatisfies height n row :=
  ⟨rectangle_row_necessary surface, rectangle_row_sufficient surface above⟩

/-- The neighborhood row is the exact inclusion-least geometric extension
for any finite history realizing the given heights. -/
theorem geometric_greedy_is_least {history : Finset Point} {height : ℕ → ℤ}
    {n access : ℕ} {time : ℤ}
    (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time) (accessBound : access < n) :
    access ∈ GreedyRow height n access ∧
    NewRectanglesSatisfied history n time (GreedyRow height n access) ∧
    ∀ row, access ∈ row → NewRectanglesSatisfied history n time row →
      GreedyRow height n access ⊆ row := by
  refine ⟨access_mem_greedyRow height accessBound,
    rectangle_row_sufficient surface above (greedyRow_satisfies height), ?_⟩
  intro row member satisfied
  exact greedyRow_subset_of_satisfies member (rectangle_row_necessary surface satisfied)

/-- The actual geometric augmentation has exactly the height update used
by the canonical refinement and gap-preservation theorems. -/
theorem augmented_has_raised_surface {history : Finset Point} {height : ℕ → ℤ}
    {n access : ℕ} {time : ℤ}
    (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time) :
    HasSurface (Augment history time (GreedyRow height n access))
      (Surface.RaiseSurface height n access time) n := by
  classical
  constructor
  · intro point member
    rcases Finset.mem_union.mp member with historical | new
    · have old := surface.1 point historical
      exact ⟨old.1, le_trans old.2 (Surface.raiseSurface_nondecreasing height time above point.1 old.1)⟩
    · obtain ⟨key, keyMember, equal⟩ := Finset.mem_image.mp new
      subst point
      have touched := mem_greedyRow.mp keyMember
      refine ⟨touched.1, ?_⟩
      simp only [Surface.RaiseSurface, if_pos touched]
      exact le_rfl
  · intro key bound
    by_cases touched : Surface.Neighborhood height n key access
    · simpa only [Surface.RaiseSurface, if_pos touched] using
        (new_mem_augment (history := history) (time := time) (mem_greedyRow.mpr touched))
    · simpa only [Surface.RaiseSurface, if_neg touched] using
        (old_mem_augment (time := time) (row := GreedyRow height n access) (surface.2 key bound))

end GreedyMerge.Geometry

#print axioms GreedyMerge.Geometry.geometric_greedy_is_least

#print axioms GreedyMerge.Geometry.augmented_has_raised_surface
