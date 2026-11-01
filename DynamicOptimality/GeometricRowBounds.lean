import DynamicOptimality.GeometricModel

/-!
# Height bounds forced by a satisfying row

A row point nearest to an old column has height at least that column's
last-touch height. Consequently, every key interval met by the row has a
maximum-height key that belongs to the row. These are geometric statements;
no BST is assumed.
-/

namespace DynamicOptimality.Geometry

open GreedyMerge.Geometry GreedyMerge.Surface

theorem nearest_row_bounds {n start old : Nat} {height : Nat → Int} {row : Finset Nat}
    (satisfied : RowSatisfies height n row) (selected : start ∈ row) (oldBound : old < n)
    (noOther : ∀ point ∈ row, Between start old point → point = start) :
    height old ≤ height start := by
  have auxiliary : ∀ distance old, Distance old start = distance → old < n →
      (∀ point ∈ row, Between start old point → point = start) → height old ≤ height start := by
    intro distance
    induction distance using Nat.strong_induction_on with
    | h distance ih =>
      intro old equal bound alone
      by_cases same : old = start
      · subst old
        exact le_rfl
      rcases satisfied.2 start selected old bound same with touched | blocked | between
      · have equal := alone old touched ⟨min_le_right _ _, le_max_right _ _⟩
        exact (same equal).elim
      · obtain ⟨blocker, inside, different, high⟩ := blocked
        have closer : Distance blocker start < distance := by
          rw [← equal]
          apply distance_strict_between
          · simpa only [min_comm] using inside.1
          · simpa only [max_comm] using inside.2
          · exact different
        have blockerBound : blocker < n := by
          have startBound := satisfied.1 start selected
          dsimp [Between] at inside
          omega
        have blockerAlone : ∀ point ∈ row, Between start blocker point → point = start := by
          intro point member near
          apply alone point member
          dsimp [Between] at inside near ⊢
          omega
        exact high.trans (ih _ closer blocker rfl blockerBound blockerAlone)
      · obtain ⟨point, member, inside, different, _⟩ := between
        exact (different (alone point member inside)).elim
  exact auxiliary _ old rfl oldBound noOther

/-- A row contains a maximum-height key of every interval that it meets. -/
theorem interval_has_selected_max {n lo hi : Nat} {height : Nat → Int} {row : Finset Nat}
    (satisfied : RowSatisfies height n row) (upper : hi ≤ n)
    (meets : ∃ key ∈ row, lo ≤ key ∧ key < hi) :
    ∃ root, root ∈ row ∧ lo ≤ root ∧ root < hi ∧
      ∀ key, lo ≤ key → key < hi → height key ≤ height root := by
  classical
  let selected := row.filter (fun key => lo ≤ key ∧ key < hi)
  have nonempty : selected.Nonempty := by
    obtain ⟨key, member, bounds⟩ := meets
    exact ⟨key, Finset.mem_filter.mpr ⟨member, bounds⟩⟩
  obtain ⟨root, rootMember, maximal⟩ := Finset.exists_max_image selected height nonempty
  have rootSpec := Finset.mem_filter.mp rootMember
  refine ⟨root, rootSpec.1, rootSpec.2.1, rootSpec.2.2, ?_⟩
  intro key keyLo keyHi
  obtain ⟨near, nearMember, nearest⟩ :=
    Finset.exists_min_image selected (fun point => Distance point key) nonempty
  have nearSpec := Finset.mem_filter.mp nearMember
  have noOther : ∀ point ∈ row, Between near key point → point = near := by
    intro point member inside
    by_contra different
    have inInterval : lo ≤ point ∧ point < hi := by
      dsimp [Between] at inside
      omega
    have candidate : point ∈ selected := Finset.mem_filter.mpr ⟨member, inInterval⟩
    have closer := distance_strict_between inside.1 inside.2 different
    have minimal := nearest point candidate
    omega
  exact (nearest_row_bounds satisfied nearSpec.1 (by omega) noOther).trans (maximal near nearMember)

end DynamicOptimality.Geometry
