import SurfaceHierarchy
import SurfaceOwners
import ExternalRealMin

/-!
The surface hierarchy's gap/separator intervals are the actual strict-height
neighborhoods used in the candidate. The inherited barrier premises hold
at the top interval and pass to each lower gap.
-/
namespace GreedyMerge.SurfaceNeighborhood
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.ExpansionRotations
open GreedyMerge.HierarchyLocality
open GreedyMerge.HierarchyExistence
open GreedyMerge.SurfaceHierarchy
open GreedyMerge.Surface

/-- No maximum separator lies in one of the original lower gaps. -/
theorem gap_excludes_separator {start n i j key : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (hl : GapLower start separator i ≤ key) (hu : key < separator i) :
    key ≠ separator j := by
  have hmono := separators_strict separator tail children
  intro heq
  subst key
  have hji : j < i := hmono.lt_iff_lt.mp hu
  cases i with
  | zero => omega
  | succ i =>
      change separator i + 1 ≤ separator j at hl
      have hij : i < j := hmono.lt_iff_lt.mp (by omega : separator i < separator j)
      omega

/-- Every original gap key has strictly lower height than its plateau. -/
theorem gap_height_lt {height : ℕ → ℤ} {start n i key : ℕ}
    (separator : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (rep : Represents height (.node separator tail children)) (hi : i ≤ n)
    (hl : GapLower start separator i ≤ key) (hu : key < separator i) :
    height key < height (separator 0) := by
  obtain ⟨hn, hmax, hcomplete, _⟩ := rep
  have hb := hierarchy_gap_bounds separator tail children hi
  have hkeyLo : start ≤ key := by omega
  have hkeyHi : key < separator n := by omega
  have hle := hmax 0 hn key hkeyLo hkeyHi
  have hne : height key ≠ height (separator 0) := by
    intro heq
    obtain ⟨j, hj, hjkey⟩ := hcomplete key hkeyLo hkeyHi heq
    exact gap_excludes_separator separator tail children hl hu hjkey
  omega

theorem separator_height_eq {height : ℕ → ℤ} {start n i j : ℕ}
    (separator : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (rep : Represents height (.node separator tail children)) (hi : i < n) (hj : j < n) :
    height (separator i) = height (separator j) := by
  have hmono := separators_strict separator tail children
  have hfirst := hierarchy_bounds (children 0 (Nat.zero_le n))
  change start ≤ separator 0 at hfirst
  have hil := hmono.monotone (Nat.zero_le i)
  have hjl := hmono.monotone (Nat.zero_le j)
  have hiu := hmono hi
  have hju := hmono hj
  exact le_antisymm (rep.2.1 j hj (separator i) (by omega) hiu)
    (rep.2.1 i hi (separator j) (by omega) hju)

/-- The two adjacent gaps plus separator are exactly its strict-height
neighborhood, including the endpoint and empty-gap cases. -/
theorem plateau_neighborhood {height : ℕ → ℤ} {keyCount start n i key : ℕ}
    (separator : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (rep : Represents height (.node separator tail children))
    (hi : i < n) (hbound : separator n ≤ keyCount)
    (lowerBarrier : start = 0 ∨ height (separator 0) ≤ height (start - 1))
    (upperBarrier : separator n = keyCount ∨ height (separator 0) ≤ height (separator n)) :
    Neighborhood height keyCount (separator i) key ↔
      GapLower start separator i ≤ key ∧ key < separator (i + 1) := by
  have hmono := separators_strict separator tail children
  have hzero := rep.1
  have hheight := separator_height_eq separator tail children rep hi hzero
  have hcLo := hierarchy_bounds (children i (by omega))
  have hcHi : separator i < separator (i + 1) := hmono (by omega)
  have hupper := hmono.monotone (by omega : i + 1 ≤ n)
  constructor
  · intro hn
    apply neighborhood_inside_barriers height hcLo hcHi (by omega) hn
    · cases i with
      | zero => simpa only [GapLower, hheight] using lowerBarrier
      | succ j =>
          right
          simp only [GapLower, Nat.add_sub_cancel]
          rw [separator_height_eq separator tail children rep hi (by omega : j < n)]
    · by_cases hlast : i + 1 = n
      · simpa only [hlast, hheight] using upperBarrier
      · right
        rw [separator_height_eq separator tail children rep hi (by omega : i + 1 < n)]
  · rintro ⟨hkeyLo, hkeyHi⟩
    have hcN : separator i < keyCount := by omega
    have hkN : key < keyCount := by omega
    refine ⟨hcN, hkN, ?_⟩
    intro blocker hbLo hbHi hne
    have hblockLo : GapLower start separator i ≤ blocker := by
      have h := Nat.le_min.mpr ⟨hcLo, hkeyLo⟩
      omega
    have hblockHi : blocker < separator (i + 1) := by
      have h := Nat.max_lt.mpr ⟨hcHi, hkeyHi⟩
      omega
    by_cases hleft : blocker < separator i
    · rw [hheight]
      exact gap_height_lt separator tail children rep (by omega) hblockLo hleft
    · have hright : separator i < blocker := by omega
      rw [hheight]
      exact gap_height_lt separator tail children rep (by omega : i + 1 ≤ n)
        (by change separator i + 1 ≤ blocker; omega) hblockHi

/-- The top-level barrier property is inherited by every original gap. -/
theorem gap_barriers {height : ℕ → ℤ} {keyCount start n i : ℕ}
    (separator : ℕ → ℕ)
    (tail : ∀ k, n ≤ k → separator k = separator n + (k - n))
    (children : ∀ k, k ≤ n → Hierarchy (GapLower start separator k) (separator k))
    (rep : Represents height (.node separator tail children))
    (hi : i ≤ n)
    (lowerBarrier : start = 0 ∨ ∀ key, start ≤ key → key < separator n →
      height key ≤ height (start - 1))
    (upperBarrier : separator n = keyCount ∨ ∀ key, start ≤ key → key < separator n →
      height key ≤ height (separator n)) :
    (GapLower start separator i = 0 ∨ ∀ key, GapLower start separator i ≤ key →
      key < separator i → height key ≤ height (GapLower start separator i - 1)) ∧
    (separator i = keyCount ∨ ∀ key, GapLower start separator i ≤ key →
      key < separator i → height key ≤ height (separator i)) := by
  have hb := hierarchy_gap_bounds separator tail children hi
  constructor
  · cases i with
    | zero =>
        rcases lowerBarrier with heq | hbar
        · exact Or.inl heq
        · right
          intro key hl hu
          exact hbar key hl (by omega)
    | succ j =>
        right
        intro key hl hu
        simp only [GapLower, Nat.add_sub_cancel]
        have hlt := gap_height_lt separator tail children rep hi hl hu
        rw [separator_height_eq separator tail children rep rep.1 (by omega : j < n)] at hlt
        omega
  · by_cases heq : i = n
    · subst i
      rcases upperBarrier with heq | hbar
      · exact Or.inl heq
      · right
        intro key hl hu
        exact hbar key (by omega) hu
    · right
      intro key hl hu
      have hlt := gap_height_lt separator tail children rep hi hl hu
      rw [separator_height_eq separator tail children rep rep.1 (by omega : i < n)] at hlt
      omega

end GreedyMerge.SurfaceNeighborhood
#print axioms GreedyMerge.SurfaceNeighborhood.plateau_neighborhood
#print axioms GreedyMerge.SurfaceNeighborhood.gap_barriers
