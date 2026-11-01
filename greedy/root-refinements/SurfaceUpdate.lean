import SurfaceTouchPaths
import GapNeighborhoods

/-!
A strict-neighborhood Greedy update raises exactly its touched keys to the
new maximum. Every off-search-path gap has no touched key; increasing the
outside heights leaves all its strict neighborhoods and comparator owners
fixed. This file proves that preservation from actual surface functions.

The input gap must carry the exact-owner and boundary facts inherited from
the old height refinement. The full search-path decomposition into all gaps
is not constructed here.
-/

namespace GreedyMerge.Surface

open Splay.Tree
open Splay.Tree.BST

theorem indicator_zero_iff (p : Prop) : Indicator p = 0 ↔ ¬p := by
  classical
  by_cases h : p <;> simp [Indicator, h]

theorem touchCount_zero_iff {lo hi n access : ℕ}
    (height : ℕ → ℤ) (tree : BST lo hi) :
    TouchCount height n access tree = 0 ↔
      ∀ key, lo ≤ key → key < hi → ¬Neighborhood height n key access := by
  classical
  induction tree with
  | empty => simp [TouchCount]; omega
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      constructor
      · intro hz
        have hroot : Indicator (Neighborhood height n root access) = 0 := by
          simp only [TouchCount] at hz
          omega
        have hleft : TouchCount height n access left = 0 := by
          simp only [TouchCount] at hz
          omega
        have hright : TouchCount height n access right = 0 := by
          simp only [TouchCount] at hz
          omega
        intro key hklo hkhi
        by_cases heq : key = root
        · simpa [heq] using (indicator_zero_iff _).1 hroot
        · by_cases hlt : key < root
          · exact ihLeft.1 hleft key hklo hlt
          · exact ihRight.1 hright key (by omega) hkhi
      · intro hnone
        have hroot := (indicator_zero_iff _).2 (hnone root hlo (by omega))
        have hleft : TouchCount height n access left = 0 :=
          ihLeft.2 (fun key hklo hkhi => hnone key hklo (by omega))
        have hright : TouchCount height n access right = 0 :=
          ihRight.2 (fun key hklo hkhi => hnone key (by omega) hkhi)
        simp only [TouchCount, hroot, hleft, hright]

noncomputable def RaiseSurface (height : ℕ → ℤ) (n access : ℕ)
    (time : ℤ) (key : ℕ) : ℤ :=
  @ite ℤ (Neighborhood height n key access)
    (Classical.propDecidable _) time (height key)

theorem raiseSurface_of_untouched (height : ℕ → ℤ) {n access key : ℕ} (time : ℤ)
    (untouched : ¬Neighborhood height n key access) :
    RaiseSurface height n access time key = height key := by
  simp [RaiseSurface, untouched]

theorem raiseSurface_nondecreasing (height : ℕ → ℤ) {n access : ℕ} (time : ℤ)
    (fresh : ∀ key, key < n → height key < time) :
    ∀ key, key < n → height key ≤ RaiseSurface height n access time key := by
  intro key hk
  classical
  by_cases h : Neighborhood height n key access
  · have hlt := fresh key hk
    simp [RaiseSurface, h]
    omega
  · simp [RaiseSurface, h]

theorem raised_top_iff_touched (height : ℕ → ℤ) {n access key : ℕ} (time : ℤ)
    (fresh : height key < time) :
    RaiseSurface height n access time key = time ↔ Neighborhood height n key access := by
  classical
  by_cases h : Neighborhood height n key access
  · simp [RaiseSurface, h]
  · have hne : height key ≠ time := by omega
    simp [RaiseSurface, h, hne]

theorem gap_has_no_touches {lo hi n access : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access)
    (exactOwners : ExactOwners rank owner tree) (hhi : hi ≤ n)
    (outside : access < lo ∨ hi ≤ access) :
    ∀ key, lo ≤ key → key < hi → ¬Neighborhood height n key access := by
  apply (touchCount_zero_iff height tree).1
  rw [touchCount_eq_ownerCount height rank owner tree owners global hhi]
  exact ownerCount_zero_of_outside rank owner tree exactOwners outside

/-- An exact-owner off-path gap keeps every internal height unchanged
during the strict-neighborhood surface update. -/
theorem offPathGap_heights_unchanged {lo hi n access : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST lo hi) (time : ℤ)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access)
    (exactOwners : ExactOwners rank owner tree) (hhi : hi ≤ n)
    (outside : access < lo ∨ hi ≤ access) :
    ∀ key, lo ≤ key → key < hi → RaiseSurface height n access time key = height key := by
  intro key hklo hkhi
  exact raiseSurface_of_untouched height time
    (gap_has_no_touches height rank owner tree owners global exactOwners hhi outside
      key hklo hkhi)

/-- The complete strict neighborhoods of gap keys remain fixed, even
though many surface heights outside the gap may rise. -/
theorem offPathGap_neighborhoods_preserved {lo hi n access center key : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST lo hi) (time : ℤ)
    (owners : Owners height rank owner n)
    (global : UniqueGlobalMinimum rank n access)
    (exactOwners : ExactOwners rank owner tree) (hhi : hi ≤ n)
    (outside : access < lo ∨ hi ≤ access)
    (fresh : ∀ z, z < n → height z < time)
    (hcenterLo : lo ≤ center) (hcenterHi : center < hi)
    (lowerBarrier : lo = 0 ∨ height center ≤ height (lo - 1))
    (upperBarrier : hi = n ∨ height center ≤ height hi) :
    Neighborhood height n center key ↔
      Neighborhood (RaiseSurface height n access time) n center key := by
  apply neighborhood_preserved_in_gap height (RaiseSurface height n access time) hhi
  · intro z hzlo hzhi
    exact (offPathGap_heights_unchanged height rank owner tree time owners global
      exactOwners hhi outside z hzlo hzhi).symm
  · exact raiseSurface_nondecreasing height time fresh
  · exact hcenterLo
  · exact hcenterHi
  · exact lowerBarrier
  · exact upperBarrier

theorem offPathGap_owners_preserved {lo hi n access center : ℕ}
    (height : ℕ → ℤ) (rank oldOwner newOwner : ℕ → ℕ) (tree : BST lo hi) (time : ℤ)
    (unique : IntervalUnique rank n)
    (oldOwners : Owners height rank oldOwner n)
    (newOwners : Owners (RaiseSurface height n access time) rank newOwner n)
    (global : UniqueGlobalMinimum rank n access)
    (exactOwners : ExactOwners rank oldOwner tree) (hhi : hi ≤ n)
    (outside : access < lo ∨ hi ≤ access)
    (fresh : ∀ z, z < n → height z < time)
    (hcenterLo : lo ≤ center) (hcenterHi : center < hi)
    (lowerBarrier : lo = 0 ∨ height center ≤ height (lo - 1))
    (upperBarrier : hi = n ∨ height center ≤ height hi) :
    oldOwner center = newOwner center := by
  apply owners_eq_of_neighborhood_eq height (RaiseSurface height n access time)
    rank oldOwner newOwner unique oldOwners newOwners (by omega)
  intro key
  exact offPathGap_neighborhoods_preserved height rank oldOwner tree time oldOwners global
    exactOwners hhi outside fresh hcenterLo hcenterHi lowerBarrier upperBarrier

end GreedyMerge.Surface

#print axioms GreedyMerge.Surface.offPathGap_owners_preserved
