import HierarchyExistence
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
The fixed hierarchy is constructed from the actual height surface: each
node lists precisely every maximum-height key of its interval, in order,
and recursively handles the intervening lower gaps. The construction is
independent of the comparator. Its canonical realization is therefore the
candidate's fixed-left-tie plateau refinement C(h,T).
-/
namespace GreedyMerge.SurfaceHierarchy
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.ExpansionRotations
open GreedyMerge.HierarchyLocality
open GreedyMerge.HierarchyExistence
open GreedyMerge.PortCases

/-- Every node contains exactly all maximal-height keys of its interval. -/
def Represents (height : ℕ → ℤ) : {lo hi : ℕ} → Hierarchy lo hi → Prop
  | _, _, .empty _ => True
  | _, _, .node (start := start) (n := n) separator _ children =>
      0 < n ∧
      (∀ i, i < n → ∀ key, start ≤ key → key < separator n → height key ≤ height (separator i)) ∧
      (∀ key, start ≤ key → key < separator n → height key = height (separator 0) →
        ∃ i, i < n ∧ key = separator i) ∧
      ∀ i (hi : i ≤ n), Represents height (children i hi)

/-- Enumerate a nonempty finite set in increasing order, then attach the
right boundary and a linear tail used only outside the finite hierarchy. -/
theorem ordered_enumeration (values : Finset ℕ) {lo hi : ℕ}
    (hne : values.Nonempty) (hinside : ∀ key, key ∈ values → lo ≤ key ∧ key < hi) :
    ∃ (n : ℕ) (separator : ℕ → ℕ), 0 < n ∧
      separator n = hi ∧ StrictMono separator ∧ lo ≤ separator 0 ∧
      (∀ i, n ≤ i → separator i = separator n + (i - n)) ∧
      (∀ i, i < n → separator i ∈ values) ∧
      (∀ key, key ∈ values → ∃ i, i < n ∧ key = separator i) := by
  classical
  let n := values.card
  have hn : 0 < n := Finset.card_pos.mpr hne
  let enumeration := values.orderEmbOfFin (k := n) rfl
  let separator := fun i => if hin : i < n then enumeration ⟨i, hin⟩ else hi + (i - n)
  have hsep_inside : ∀ i (h : i < n), separator i = enumeration ⟨i, h⟩ := by
    intro i h
    simp only [separator, dif_pos h]
  have hsep_mem : ∀ i, i < n → separator i ∈ values := by
    intro i h
    rw [hsep_inside i h]
    exact values.orderEmbOfFin_mem rfl ⟨i, h⟩
  have hsep_last : separator n = hi := by simp [separator]
  have hsep_tail : ∀ i, n ≤ i → separator i = separator n + (i - n) := by
    intro i h
    rw [hsep_last]
    simp only [separator, dif_neg (by omega : ¬i < n)]
  have hsep_mono : StrictMono separator := by
    apply strictMono_nat_of_lt_succ
    intro i
    by_cases hnext : i + 1 < n
    · have hprev : i < n := by omega
      rw [hsep_inside i hprev, hsep_inside (i + 1) hnext]
      apply enumeration.strictMono
      change i < i + 1
      omega
    · by_cases hprev : i < n
      · have hboundary : i + 1 = n := by omega
        rw [hboundary, hsep_last]
        exact (hinside _ (hsep_mem i hprev)).2
      · rw [hsep_tail i (by omega), hsep_tail (i + 1) (by omega)]
        omega
  refine ⟨n, separator, hn, hsep_last, hsep_mono,
    (hinside _ (hsep_mem 0 hn)).1, hsep_tail, hsep_mem, ?_⟩
  intro key hkey
  let index : Fin n := (values.orderIsoOfFin rfl).symm ⟨key, hkey⟩
  refine ⟨index.val, index.isLt, ?_⟩
  rw [hsep_inside index.val index.isLt]
  have heq := congrArg Subtype.val ((values.orderIsoOfFin rfl).apply_symm_apply ⟨key, hkey⟩)
  exact heq.symm

/-- Construct the actual maximum-height hierarchy for any finite surface. -/
theorem exists_surface_hierarchy (height : ℕ → ℤ) (lo hi : ℕ) (horder : lo ≤ hi) :
    ∃ hierarchy : Hierarchy lo hi, Represents height hierarchy := by
  classical
  generalize hsize : hi - lo = size
  induction size using Nat.strong_induction_on generalizing lo hi with
  | h size ih =>
      by_cases heq : lo = hi
      · subst hi
        exact ⟨.empty lo, trivial⟩
      · have hlt : lo < hi := by omega
        have hnonempty : (Finset.Ico lo hi).Nonempty := ⟨lo, by simp [hlt]⟩
        obtain ⟨top, htopMem, hmax⟩ := Finset.exists_max_image (Finset.Ico lo hi) height hnonempty
        let maxima := (Finset.Ico lo hi).filter fun key => height key = height top
        have hmaxima : maxima.Nonempty := ⟨top, by simp [maxima, htopMem]⟩
        have hmaxInside : ∀ key, key ∈ maxima → lo ≤ key ∧ key < hi := by
          intro key hk
          exact Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1
        obtain ⟨n, separator, hn, hlast, hmono, hfirst, htail, hmember, honto⟩ :=
          ordered_enumeration maxima hmaxima hmaxInside
        have hsepHeight : ∀ i, i < n → height (separator i) = height top := by
          intro i hi
          exact (Finset.mem_filter.mp (hmember i hi)).2
        have gapFacts : ∀ i, i ≤ n →
            lo ≤ GapLower lo separator i ∧ GapLower lo separator i ≤ separator i ∧
            separator i ≤ hi ∧ separator i - GapLower lo separator i < size := by
          intro i hin
          have upper : separator i ≤ hi := by
            have h := hmono.monotone hin
            omega
          cases i with
          | zero =>
              have hupper := (hmaxInside _ (hmember 0 hn)).2
              simp only [GapLower]
              omega
          | succ i =>
              have hlow := hmono.monotone (Nat.zero_le i)
              have hstrict := hmono (by omega : i < i + 1)
              simp only [GapLower]
              omega
        have childExists : ∀ i (hin : i ≤ n), ∃ hierarchy : Hierarchy (GapLower lo separator i) (separator i),
            Represents height hierarchy := by
          intro i hin
          have hgap := gapFacts i hin
          exact ih (separator i - GapLower lo separator i) hgap.2.2.2
            (GapLower lo separator i) (separator i) hgap.2.1 rfl
        let children := fun i hin => Classical.choose (childExists i hin)
        have hchildren : ∀ i (hin : i ≤ n), Represents height (children i hin) := by
          intro i hin
          exact Classical.choose_spec (childExists i hin)
        have hrep : Represents height (Hierarchy.node separator htail children) := by
          refine ⟨hn, ?_, ?_, hchildren⟩
          · intro i hin key hklo hkhi
            rw [hsepHeight i hin]
            exact hmax key (Finset.mem_Ico.mpr ⟨hklo, by omega⟩)
          · intro key hklo hkhi hheight
            have hmem : key ∈ maxima := by
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_Ico.mpr ⟨hklo, by omega⟩, ?_⟩
              exact hheight.trans (hsepHeight 0 hn)
            exact honto key hmem
        cases hlast
        exact ⟨.node separator htail children, hrep⟩

noncomputable def ofSurface (height : ℕ → ℤ) (lo hi : ℕ) (horder : lo ≤ hi) : Hierarchy lo hi :=
  Classical.choose (exists_surface_hierarchy height lo hi horder)

theorem ofSurface_represents (height : ℕ → ℤ) (lo hi : ℕ) (horder : lo ≤ hi) :
    Represents height (ofSurface height lo hi horder) :=
  Classical.choose_spec (exists_surface_hierarchy height lo hi horder)

noncomputable def surfaceCanonical {n : ℕ} (height : ℕ → ℤ) (comparator : BST 0 n) : BST 0 n :=
  canonical comparator (ofSurface height 0 n (Nat.zero_le n)) (Nat.le_refl _) (Nat.le_refl _)

/-- Unconditional sharp locality for the actual recursively defined,
left-tie canonical refinement of an arbitrary finite height surface. -/
theorem surfaceCanonical_rotation {n a b depth : ℕ} (height : ℕ → ℤ)
    {before after : BST 0 n} (step : GreedyMerge.KeyRotationAt a b depth before after) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps
      (surfaceCanonical height before) (surfaceCanonical height after) :=
  canonical_rotation step (ofSurface height 0 n (Nat.zero_le n)) (Nat.le_refl _) (Nat.le_refl _)

end GreedyMerge.SurfaceHierarchy

#print axioms GreedyMerge.SurfaceHierarchy.exists_surface_hierarchy
#print axioms GreedyMerge.SurfaceHierarchy.surfaceCanonical_rotation
