import SurfaceNeighborhood
import CanonicalSurface

/-!
Identification of the independently constructed canonical surface map with
Surface.Canonical, the exact height/owner-rank/left-tie predicate used by
the direct touch-path and exact-owner formalizations.
-/
namespace GreedyMerge.CanonicalBridge
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.ExpansionRotations
open GreedyMerge.PlateauBridge
open GreedyMerge.HierarchyLocality
open GreedyMerge.HierarchyExistence
open GreedyMerge.SurfaceHierarchy
open GreedyMerge.SurfaceNeighborhood
open GreedyMerge.ExternalRealMin
open GreedyMerge.PortCases

/-- Expanding a separator Cartesian tree and canonical lower gaps gives
the global height/priority/left-tie canonical tree. -/
theorem expand_canonical {height : ℕ → ℤ} {priority atoms : ℕ → ℕ}
    {start n lo hi : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (rep : Represents height (.node separator tail children))
    (gaps : ∀ k, BST (GapLower start separator k) (separator k))
    (gapCanonical : ∀ k, k ≤ n → GreedyMerge.Surface.Canonical height priority (gaps k))
    (priorityEq : ∀ k, k < n → priority (separator k) = Priority atoms k)
    (skeleton : BST lo hi) (hhi : hi ≤ n)
    (hcanonical : GreedyMerge.IntervalRootOracle.Canonical atoms skeleton) :
    GreedyMerge.Surface.Canonical height priority (Expand start separator gaps skeleton) := by
  have hmono := separators_strict separator tail children
  induction skeleton with
  | empty boundary => exact gapCanonical boundary hhi
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hroot, hleft, hright⟩ := hcanonical
      have hrlo := left.lower_le_upper
      have hrhi := right.lower_le_upper
      have hrn : root < n := by omega
      have hb := hierarchy_gap_bounds separator tail children (show lo ≤ n by omega)
      have hheight := separator_height_eq separator tail children rep hrn rep.1
      have hglo : start ≤ GapLower start separator lo := hb.1
      have hghi : separator hi ≤ separator n := hmono.monotone hhi
      have locateMax : ∀ key, GapLower start separator lo ≤ key → key < separator hi →
          height key = height (separator root) →
          ∃ j, lo ≤ j ∧ j < hi ∧ key = separator j := by
        intro key hkl hku hheightKey
        obtain ⟨j, hjn, heq⟩ := rep.2.2.1 key (by omega) (by omega) (hheightKey.trans hheight)
        have hjhi : j < hi := hmono.lt_iff_lt.mp (heq ▸ hku)
        have hjlo : lo ≤ j := by
          cases lo with
          | zero => omega
          | succ lo =>
              change separator lo + 1 ≤ key at hkl
              have hx : lo < j := hmono.lt_iff_lt.mp (by omega : separator lo < separator j)
              omega
        exact ⟨j, hjlo, hjhi, heq⟩
      change GreedyMerge.Surface.Canonical height priority
        (.node (Expand start separator gaps left) (Expand start separator gaps right))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro key hkl hku
        exact rep.2.1 root hrn key (by omega) (by omega)
      · intro key hkl hku hh
        obtain ⟨j, hjlo, hjhi, heq⟩ := locateMax key hkl hku hh
        rw [heq, priorityEq root hrn, priorityEq j (by omega)]
        exact hroot.2.2.1 j hjlo hjhi
      · intro key hkl hku hh hp
        obtain ⟨j, hjlo, hjhi, heq⟩ := locateMax key hkl hku hh
        rw [heq, priorityEq j (by omega), priorityEq root hrn] at hp
        have hrj : root ≤ j := by
          by_contra hn
          have hlt := hroot.2.2.2 j hjlo (by omega)
          omega
        rw [heq]
        exact hmono.monotone hrj
      · exact ihLeft (by omega) hleft
      · exact ihRight hhi hright

/-- The triple-of-atoms priority is exactly the ordinary rank of the
actual strict-neighborhood owner; null records cause no discrepancy. -/
theorem plateau_priority_eq {height : ℕ → ℤ} {keyCount start n i : ℕ}
    (comparator : BST 0 keyCount) (separator gapOwner owner : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (rep : Represents height (.node separator tail children))
    (owners : GreedyMerge.Surface.Owners height comparator.depth owner keyCount)
    (hi : i < n) (hbound : separator n ≤ keyCount)
    (lowerBarrier : start = 0 ∨ height (separator 0) ≤ height (start - 1))
    (upperBarrier : separator n = keyCount ∨ height (separator 0) ≤ height (separator n))
    (minima : ∀ k, k ≤ n → UniqueMin comparator.externalDepth
      (2 * GapLower start separator k) (2 * separator k) (gapOwner k)) :
    Priority (fun atom => comparator.externalDepth (AtomOwner separator gapOwner atom)) i =
      comparator.depth (owner (separator i)) := by
  have hmono := separators_strict separator tail children
  have hcenter : separator i < keyCount := by have h := hmono hi; omega
  have hneighborhood : ∀ key, GreedyMerge.Surface.Neighborhood height keyCount (separator i) key ↔
      GapLower start separator i ≤ key ∧ key < separator (i + 1) := by
    intro key
    exact plateau_neighborhood separator tail children rep hi hbound lowerBarrier upperBarrier
  obtain ⟨hvisible, hownerMin⟩ := owners (separator i) hcenter
  have hownerRange := (hneighborhood _).mp hvisible
  have hcLo := hierarchy_bounds (children i (by omega))
  have hcHi : separator i < separator (i + 1) := hmono (by omega)
  have hhi : separator (i + 1) ≤ keyCount := by
    have h := hmono.monotone (show i + 1 ≤ n by omega)
    omega
  have hrealMin : IsIntervalMin comparator.depth (GapLower start separator i)
      (separator (i + 1) - 1) (owner (separator i)) := by
    refine ⟨hownerRange.1, by omega, ?_⟩
    intro key hkl hku
    exact hownerMin key ((hneighborhood _).mpr ⟨hkl, by omega⟩)
  have hwhole := intervalMin_external_of_real comparator (Nat.zero_le _) hhi (by omega) hrealMin
  have hleft := minima i (by omega)
  have hright := minima (i + 1) (by omega)
  have hrlo : 2 * (separator i + 1) ≤ gapOwner (i + 1) := hright.1.1
  have hh := hwhole.2.2
  have hx0 := hh (gapOwner i) hleft.1.1 (by have h := hleft.1.2.1; omega)
  have hx1 := hh (2 * separator i + 1) (by omega) (by omega)
  have hx2 := hh (gapOwner (i + 1)) (by omega) hright.1.2.1
  have hformula : Priority (fun atom => comparator.externalDepth (AtomOwner separator gapOwner atom)) i =
      min (comparator.externalDepth (gapOwner i))
        (min (comparator.externalDepth (2 * separator i + 1))
          (comparator.externalDepth (gapOwner (i + 1)))) := by
    unfold Priority
    dsimp only
    rw [owner_even, owner_odd, show 2 * i + 2 = 2 * (i + 1) by omega, owner_even]
  rw [hformula, ← externalDepth_real comparator (owner (separator i))]
  apply Nat.le_antisymm
  · by_cases hl : owner (separator i) < separator i
    · exact Nat.le_trans (Nat.min_le_left _ _) (hleft.1.2.2 _ (by omega) (by omega))
    · by_cases heq : owner (separator i) = separator i
      · rw [heq]
        exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
      · exact Nat.le_trans (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))
          (hright.1.2.2 _ (by change 2 * (separator i + 1) ≤ _; omega) (by omega))
  · exact Nat.le_min.mpr ⟨hx0, Nat.le_min.mpr ⟨hx1, hx2⟩⟩


/-- The recursively constructed realization satisfies exactly the direct
height/owner-rank/left-tie canonical predicate, with inherited barriers. -/
theorem realizes_canonical {height : ℕ → ℤ} {keyCount lo hi : ℕ}
    (comparator : BST 0 keyCount) (owner : ℕ → ℕ)
    (owners : GreedyMerge.Surface.Owners height comparator.depth owner keyCount)
    (hierarchy : Hierarchy lo hi) (tree : BST lo hi)
    (rep : Represents height hierarchy) (hhi : hi ≤ keyCount)
    (lowerBarrier : lo = 0 ∨ ∀ key, lo ≤ key → key < hi → height key ≤ height (lo - 1))
    (upperBarrier : hi = keyCount ∨ ∀ key, lo ≤ key → key < hi → height key ≤ height hi)
    (realizes : Realizes comparator.externalDepth hierarchy tree) :
    GreedyMerge.Surface.Canonical height (fun key => comparator.depth (owner key)) tree := by
  induction hierarchy with
  | empty boundary =>
      change tree = .empty boundary at realizes
      rw [realizes]
      trivial
  | @node start n separator tail children ih =>
      obtain ⟨gaps, gapOwner, skeleton, subtrees, minima, hcanonical, htree⟩ := realizes
      have hmono := separators_strict separator tail children
      have hfirst := hierarchy_bounds (children 0 (Nat.zero_le n))
      change start ≤ separator 0 at hfirst
      have hlast := hmono rep.1
      have hlow : start = 0 ∨ height (separator 0) ≤ height (start - 1) := by
        rcases lowerBarrier with heq | hbar
        · exact Or.inl heq
        · exact Or.inr (hbar _ hfirst hlast)
      have hupp : separator n = keyCount ∨ height (separator 0) ≤ height (separator n) := by
        rcases upperBarrier with heq | hbar
        · exact Or.inl heq
        · exact Or.inr (hbar _ hfirst hlast)
      have gapCanon : ∀ k, k ≤ n → GreedyMerge.Surface.Canonical height
          (fun key => comparator.depth (owner key)) (gaps k) := by
        intro k hk
        have hb := hierarchy_gap_bounds separator tail children hk
        have bars := gap_barriers separator tail children rep hk lowerBarrier upperBarrier
        exact ih k hk (gaps k) (rep.2.2.2 k hk) (by omega) bars.1 bars.2 (subtrees k hk)
      have priorities : ∀ k, k < n → comparator.depth (owner (separator k)) =
          Priority (fun atom => comparator.externalDepth (AtomOwner separator gapOwner atom)) k := by
        intro k hk
        exact (plateau_priority_eq comparator separator gapOwner owner tail children rep owners
          hk hhi hlow hupp minima).symm
      rw [htree]
      exact expand_canonical separator tail children rep gaps gapCanon priorities skeleton
        (Nat.le_refl n) hcanonical

/-- The total canonical map from the independent locality development is
the very same canonical tree used by SurfaceTouchPaths and SubtreeGap. -/
theorem surfaceCanonical_isCanonical {height : ℕ → ℤ} {keyCount : ℕ}
    (comparator : BST 0 keyCount) (owner : ℕ → ℕ)
    (owners : GreedyMerge.Surface.Owners height comparator.depth owner keyCount) :
    GreedyMerge.Surface.Canonical height (fun key => comparator.depth (owner key))
      (surfaceCanonical height comparator) := by
  exact realizes_canonical comparator owner owners
    (ofSurface height 0 keyCount (Nat.zero_le keyCount)) _
    (ofSurface_represents height 0 keyCount (Nat.zero_le keyCount))
    (Nat.le_refl _) (Or.inl rfl) (Or.inl rfl)
    (canonical_realizes comparator _ (Nat.le_refl _) (Nat.le_refl _))

/-- A concrete comparator rotation changes the candidate's exact canonical
refinement by at most two ordinary BST rotations. All input predicates are
the direct height/strict-neighborhood definitions, with no hierarchy,
projection, fringe, owner-change, or lifetime premise. -/
theorem actual_canonical_rotation {height : ℕ → ℤ} {keyCount a b depth : ℕ}
    {before after : BST 0 keyCount}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height before.depth oldOwner keyCount)
    (newOwners : GreedyMerge.Surface.Owners height after.depth newOwner keyCount)
    (oldTree newTree : BST 0 keyCount)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => before.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical height
      (fun key => after.depth (newOwner key)) newTree) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps oldTree newTree := by
  have heqOld := GreedyMerge.Surface.canonical_unique height
    (fun key => before.depth (oldOwner key)) oldTree (surfaceCanonical height before)
    oldCanonical (surfaceCanonical_isCanonical before oldOwner oldOwners)
  have heqNew := GreedyMerge.Surface.canonical_unique height
    (fun key => after.depth (newOwner key)) newTree (surfaceCanonical height after)
    newCanonical (surfaceCanonical_isCanonical after newOwner newOwners)
  rw [heqOld, heqNew]
  exact surfaceCanonical_rotation height step


/-- The same theorem for the ordinary unlabelled comparator rotation API. -/
theorem actual_canonical_rotationAt {height : ℕ → ℤ} {keyCount depth : ℕ}
    {before after : BST 0 keyCount} (step : RotationAt depth before after)
    (oldOwner newOwner : ℕ → ℕ)
    (oldOwners : GreedyMerge.Surface.Owners height before.depth oldOwner keyCount)
    (newOwners : GreedyMerge.Surface.Owners height after.depth newOwner keyCount)
    (oldTree newTree : BST 0 keyCount)
    (oldCanonical : GreedyMerge.Surface.Canonical height
      (fun key => before.depth (oldOwner key)) oldTree)
    (newCanonical : GreedyMerge.Surface.Canonical height
      (fun key => after.depth (newOwner key)) newTree) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps oldTree newTree := by
  obtain ⟨a, b, keyed⟩ := GreedyMerge.exists_keyRotationAt step
  exact actual_canonical_rotation keyed oldOwner newOwner oldOwners newOwners
    oldTree newTree oldCanonical newCanonical

end GreedyMerge.CanonicalBridge
#print axioms GreedyMerge.CanonicalBridge.expand_canonical
#print axioms GreedyMerge.CanonicalBridge.plateau_priority_eq

#print axioms GreedyMerge.CanonicalBridge.surfaceCanonical_isCanonical
#print axioms GreedyMerge.CanonicalBridge.actual_canonical_rotation

#print axioms GreedyMerge.CanonicalBridge.actual_canonical_rotationAt
