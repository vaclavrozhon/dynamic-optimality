import HierarchyLocality

/-!
Existence, uniqueness, and a total canonical map for recursive ordered
hierarchies. These results discharge the Realizes hypotheses of the sharp
locality theorem for every concrete comparator containing the key interval.
-/
namespace GreedyMerge.HierarchyExistence
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.OrderedAtoms
open GreedyMerge.ComparatorAtoms
open GreedyMerge.ExpansionRotations
open GreedyMerge.PlateauBridge
open GreedyMerge.HierarchyLocality
open GreedyMerge.PortCases

theorem hierarchy_bounds {lo hi : ℕ} (hierarchy : Hierarchy lo hi) : lo ≤ hi := by
  induction hierarchy with
  | empty => omega
  | @node start n separator tail children ih =>
      have hstart := ih 0 (Nat.zero_le n)
      change start ≤ separator 0 at hstart
      have hsep : StrictMono separator := by
        apply strictMono_nat_of_lt_succ
        intro i
        by_cases hin : i < n
        · have h := ih (i + 1) (by omega)
          change separator i + 1 ≤ separator (i + 1) at h
          omega
        · rw [tail i (by omega), tail (i + 1) (by omega)]
          omega
      have hlast := hsep.monotone (Nat.zero_le n)
      omega

theorem separators_strict {start n : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ i, n ≤ i → separator i = separator n + (i - n))
    (children : ∀ i, i ≤ n → Hierarchy (GapLower start separator i) (separator i)) :
    StrictMono separator := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hin : i < n
  · have h := hierarchy_bounds (children (i + 1) (by omega))
    change separator i + 1 ≤ separator (i + 1) at h
    omega
  · rw [tail i (by omega), tail (i + 1) (by omega)]
    omega

theorem hierarchy_gap_bounds {start n i : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ j, n ≤ j → separator j = separator n + (j - n))
    (children : ∀ j, j ≤ n → Hierarchy (GapLower start separator j) (separator j))
    (hi : i ≤ n) : start ≤ GapLower start separator i ∧ separator i ≤ separator n := by
  have hsep := separators_strict separator tail children
  have hstart := hierarchy_bounds (children 0 (Nat.zero_le n))
  change start ≤ separator 0 at hstart
  constructor
  · cases i with
    | zero => exact Nat.le_refl _
    | succ i =>
        change start ≤ separator i + 1
        have h := hsep.monotone (Nat.zero_le i)
        omega
  · exact hsep.monotone hi

theorem tail_gap_empty {start n i : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ j, n ≤ j → separator j = separator n + (j - n))
    (hi : n < i) : GapLower start separator i = separator i := by
  cases i with
  | zero => omega
  | succ i =>
      change separator i + 1 = separator (i + 1)
      rw [tail i (by omega), tail (i + 1) (by omega)]
      omega

noncomputable def completeGaps {start n : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ j, n ≤ j → separator j = separator n + (j - n))
    (inside : ∀ i, i ≤ n → BST (GapLower start separator i) (separator i))
    (i : ℕ) : BST (GapLower start separator i) (separator i) :=
  if hi : i ≤ n then inside i hi else by
    rw [tail_gap_empty separator tail (by omega : n < i)]
    exact .empty _

theorem completeGaps_inside {start n i : ℕ} (separator : ℕ → ℕ)
    (tail : ∀ j, n ≤ j → separator j = separator n + (j - n))
    (inside : ∀ j, j ≤ n → BST (GapLower start separator j) (separator j))
    (hi : i ≤ n) : completeGaps separator tail inside i = inside i hi := by
  simp only [completeGaps, dif_pos hi]

theorem exists_skeleton {treeLo treeHi start n : ℕ}
    (comparator : BST treeLo treeHi) (separator owner : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower start separator i) (separator i))
    (hl : treeLo ≤ start) (hu : separator n ≤ treeHi)
    (minima : ∀ i, i ≤ n → UniqueMin comparator.externalDepth
      (2 * GapLower start separator i) (2 * separator i) (owner i)) :
    ∃ skeleton : BST 0 n,
      Canonical (fun atom => comparator.externalDepth (AtomOwner separator owner atom)) skeleton := by
  apply exists_canonical _ 0 n (Nat.zero_le n)
  intro lo hi hlow hnonempty hhigh
  have hcut := cut_strictMono start separator gaps
  have hleft := hcut.monotone (by omega : 0 ≤ 2 * lo)
  have hright := hcut.monotone (by omega : 2 * hi + 1 ≤ 2 * n + 1)
  have hstrict := hcut (by omega : 2 * lo < 2 * hi + 1)
  rw [cut_zero] at hleft
  rw [cut_odd, cut_odd] at hright
  obtain ⟨key, hm⟩ := exists_uniqueMin_external comparator
    (by omega : 2 * treeLo ≤ Cut start separator (2 * lo))
    (by omega : Cut start separator (2 * lo) ≤ Cut start separator (2 * hi + 1) - 1)
    (by rw [cut_odd]; omega : Cut start separator (2 * hi + 1) - 1 ≤ 2 * treeHi)
  have hc := contract_min hcut (gap_owners_are_atom_owners minima)
    (by omega : 2 * lo ≤ 2 * hi) (by omega : 2 * hi < 2 * n + 1) hm
  exact ⟨_, hc, hc⟩

/-- Every ordered hierarchy has a concrete canonical realization for every
containing comparator. This discharges all recursive realization premises. -/
theorem exists_realization {treeLo treeHi lo hi : ℕ}
    (comparator : BST treeLo treeHi) (hierarchy : Hierarchy lo hi)
    (hl : treeLo ≤ lo) (hu : hi ≤ treeHi) :
    ∃ tree : BST lo hi, Realizes comparator.externalDepth hierarchy tree := by
  classical
  induction hierarchy with
  | empty boundary => exact ⟨.empty boundary, rfl⟩
  | @node start n separator tail children ih =>
      have childExists : ∀ i (hi : i ≤ n), ∃ tree,
          Realizes comparator.externalDepth (children i hi) tree := by
        intro i hi
        have hb := hierarchy_gap_bounds separator tail children hi
        exact ih i hi (by omega) (by omega)
      let inside := fun i hi => Classical.choose (childExists i hi)
      let gaps := completeGaps separator tail inside
      have subtrees : ∀ i (hi : i ≤ n), Realizes comparator.externalDepth (children i hi) (gaps i) := by
        intro i hi
        have hreal := Classical.choose_spec (childExists i hi)
        change Realizes comparator.externalDepth (children i hi) (completeGaps separator tail inside i)
        rw [completeGaps_inside separator tail inside hi]
        exact hreal
      have minExists : ∀ i, i ≤ n → ∃ key, UniqueMin comparator.externalDepth
          (2 * GapLower start separator i) (2 * separator i) key := by
        intro i hi
        have hb := hierarchy_gap_bounds separator tail children hi
        have hgap := hierarchy_bounds (children i hi)
        exact exists_uniqueMin_external comparator (by omega) (by omega) (by omega)
      let owner := fun i => if hi : i ≤ n then Classical.choose (minExists i hi) else 0
      have minima : ∀ i, i ≤ n → UniqueMin comparator.externalDepth
          (2 * GapLower start separator i) (2 * separator i) (owner i) := by
        intro i hi
        dsimp only [owner]
        rw [dif_pos hi]
        exact Classical.choose_spec (minExists i hi)
      obtain ⟨skeleton, hcanonical⟩ := exists_skeleton comparator separator owner gaps hl hu minima
      exact ⟨Expand start separator gaps skeleton,
        gaps, owner, skeleton, subtrees, minima, hcanonical, rfl⟩

theorem realization_unique {treeLo treeHi lo hi : ℕ}
    (comparator : BST treeLo treeHi) (hierarchy : Hierarchy lo hi)
    (first second : BST lo hi)
    (hf : Realizes comparator.externalDepth hierarchy first)
    (hs : Realizes comparator.externalDepth hierarchy second)
    (hl : treeLo ≤ lo) (hu : hi ≤ treeHi) : first = second := by
  apply realizes_eq_of_recordSame hierarchy first second hf hs
  intro l u hll hlu huu
  obtain ⟨owner, hm⟩ := exists_uniqueMin_external comparator (by omega) hlu (by omega)
  exact ⟨owner, owner, hm, hm, Or.inl rfl⟩

noncomputable def canonical {treeLo treeHi lo hi : ℕ}
    (comparator : BST treeLo treeHi) (hierarchy : Hierarchy lo hi)
    (hl : treeLo ≤ lo) (hu : hi ≤ treeHi) : BST lo hi :=
  Classical.choose (exists_realization comparator hierarchy hl hu)

theorem canonical_realizes {treeLo treeHi lo hi : ℕ}
    (comparator : BST treeLo treeHi) (hierarchy : Hierarchy lo hi)
    (hl : treeLo ≤ lo) (hu : hi ≤ treeHi) :
    Realizes comparator.externalDepth hierarchy (canonical comparator hierarchy hl hu) :=
  Classical.choose_spec (exists_realization comparator hierarchy hl hu)

/-- A total-map version of sharp canonical locality for complete ordered
hierarchies and actual comparator rotations, at arbitrary depth. -/
theorem canonical_rotation {treeLo treeHi lo hi a b depth : ℕ}
    {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (hierarchy : Hierarchy lo hi) (hl : treeLo ≤ lo) (hu : hi ≤ treeHi) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps
      (canonical before hierarchy hl hu) (canonical after hierarchy hl hu) :=
  hierarchy_rotation step hierarchy _ _
    (canonical_realizes before hierarchy hl hu) (canonical_realizes after hierarchy hl hu) hl hu

end GreedyMerge.HierarchyExistence

#print axioms GreedyMerge.HierarchyExistence.exists_realization
#print axioms GreedyMerge.HierarchyExistence.canonical_rotation

#print axioms GreedyMerge.HierarchyExistence.realization_unique
