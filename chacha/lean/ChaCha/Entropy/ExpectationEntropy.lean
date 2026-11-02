import ChaCha.Entropy.ExpectationReference
import ChaCha.Entropy.ExpectationDistribution
import ChaCha.Entropy.WeightedMedianReference
import ChaCha.Entropy.Deterministic
import Mathlib.Data.Finset.Sort

/-!
# Entropy completeness of the actual residual bound

The histogram determines the ordered auxiliary reference before the random
permutation is drawn. The expectation uses the explicit uniform probability
space of occurrence permutations. The final inequality has the manuscript's
coefficient `2 log₂(3)` and includes the empty word.
-/

namespace ChaCha.Entropy

open PreferredProjection Paper20261030.Dyadic

def histogramKeys (base : List Int) : List Int := base.toFinset.sort (· ≤ ·)

@[simp] theorem mem_histogramKeys (base : List Int) (key : Int) :
    key ∈ histogramKeys base ↔ key ∈ base := by simp [histogramKeys]

theorem histogramKeys_nodup (base : List Int) : (histogramKeys base).Nodup :=
  base.toFinset.sort_nodup _

theorem histogramKeys_ordered (base : List Int) : (histogramKeys base).Pairwise (· < ·) :=
  base.toFinset.sortedLT_sort.pairwise

theorem histogram_weight (base : List Int) : weight base.count (histogramKeys base) = base.length := by
  rw [weight_count base (histogramKeys base) (histogramKeys_nodup base)]
  rw [List.filter_eq_self.mpr (by intro key present; exact decide_eq_true ((mem_histogramKeys _ _).mpr present))]

/-- This is `m H(f/m)`, in bits rather than natural-log units. -/
noncomputable def histogramEntropyBits (base : List Int) : ℝ :=
  entropyMass base.count (histogramKeys base) / Real.log 2

theorem exists_entropy_auxiliary (base : List Int) :
    ∃ auxiliary : PrefRouter Int, auxiliary.leaves.Pairwise (· < ·) ∧
      (∀ key ∈ base, key ∈ auxiliary.leaves) ∧
      entropyMass base.count (histogramKeys base) ≤ Real.log 3 *
        (2*shuffleExpectation base (fun word => (auxiliary.primaryWilber word:ℝ))+(base.length:ℝ)) := by
  by_cases empty : base = []
  · subst base
    refine ⟨.leaf 0,by simp [PrefRouter.leaves],by simp,?_⟩
    simp [histogramKeys,shuffleExpectation,PrefRouter.primaryWilber]
  · have keyNonempty : histogramKeys base ≠ [] := by
      intro missing
      have noKey : ∀ key, key ∉ base := by
        intro key present
        have belongs := (mem_histogramKeys base key).mpr present
        simpa only [missing,List.not_mem_nil] using belongs
      cases base with
      | nil => exact empty rfl
      | cons key word => exact noKey key List.mem_cons_self
    have positive : ∀ key ∈ histogramKeys base, 0 < base.count key := by
      intro key present
      exact List.count_pos_iff.mpr ((mem_histogramKeys base key).mp present)
    obtain ⟨auxiliary,leaves,ordered,bound⟩ := exists_ordered_weighted_reference base.count
      (histogramKeys base) keyNonempty (histogramKeys_ordered base) positive
    refine ⟨auxiliary,ordered,?_,?_⟩
    · intro key present
      rw [leaves]
      exact (mem_histogramKeys base key).mpr present
    · have nodup : auxiliary.leaves.Nodup := by rw [leaves]; exact histogramKeys_nodup base
      rw [← primary_expectation base auxiliary nodup,histogram_weight] at bound
      exact bound

theorem expected_residual_domination {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (auxiliary : PrefRouter Int) (base : List Int)
    (primaryKeys : ∀ key ∈ base, key ∈ primary.leaves)
    (auxiliaryKeys : ∀ key ∈ base, key ∈ auxiliary.leaves) :
    (base.length:ℝ)+shuffleExpectation base (fun word => (auxiliary.primaryWilber word:ℝ)) ≤
      shuffleExpectation base (fun word => (residualBound primary depth auxiliary word:ℝ)) := by
  have pointwise (sample : ShuffleSample base) :
      (base.length:ℝ)+(auxiliary.primaryWilber (sampleWord base sample):ℝ) ≤
        (residualBound primary depth auxiliary (sampleWord base sample):ℝ) := by
    have bounds := residual_domination primary depth auxiliary (sampleWord base sample)
      (fun key present => primaryKeys key ((sampleWord_perm base sample).mem_iff.mp present))
      (fun key present => auxiliaryKeys key ((sampleWord_perm base sample).mem_iff.mp present))
    have lower := (le_max_right _ _).trans bounds
    rw [sampleWord_length] at lower
    exact_mod_cast lower
  have averaged := uniformMean_mono pointwise
  rw [uniformMean_add,uniformMean_const] at averaged
  exact averaged

/-- For the histogram-dependent ordered auxiliary reference, the expected
residual dominates `m(1+H)` up to exactly `2 log₂(3)`. The original primary
and depth references remain unchanged. -/
theorem exists_expected_residual_entropy {a b : Nat} (primary : PrefRouter Int) (depth : DepthTree a b)
    (base : List Int) (primaryKeys : ∀ key ∈ base, key ∈ primary.leaves) :
    ∃ auxiliary : PrefRouter Int, auxiliary.leaves.Pairwise (· < ·) ∧
      (∀ key ∈ base, key ∈ auxiliary.leaves) ∧
      (base.length:ℝ)+histogramEntropyBits base ≤
        2*(Real.log 3/Real.log 2)*
          shuffleExpectation base (fun word => (residualBound primary depth auxiliary word:ℝ)) := by
  obtain ⟨auxiliary,ordered,keys,entropy⟩ := exists_entropy_auxiliary base
  refine ⟨auxiliary,ordered,keys,?_⟩
  have domination := expected_residual_domination primary depth auxiliary base primaryKeys keys
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have logThree : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num : (1:ℝ)<3)).le
  have logs : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have scaled : (base.length:ℝ)*Real.log 2 + entropyMass base.count (histogramKeys base) ≤
      2*Real.log 3*shuffleExpectation base (fun word => (residualBound primary depth auxiliary word:ℝ)) := by
    have multiplied := mul_le_mul_of_nonneg_left domination logThree
    have lengthBound := mul_le_mul_of_nonneg_left logs (Nat.cast_nonneg base.length : (0:ℝ)≤base.length)
    nlinarith
  unfold histogramEntropyBits
  calc
    _ = ((base.length:ℝ)*Real.log 2+entropyMass base.count (histogramKeys base))/Real.log 2 := by
      field_simp [ne_of_gt logTwo]
    _ ≤ (2*Real.log 3*shuffleExpectation base
        (fun word => (residualBound primary depth auxiliary word:ℝ)))/Real.log 2 :=
      div_le_div_of_nonneg_right scaled logTwo.le
    _ = _ := by ring

/-- A single histogram-chosen auxiliary reference simultaneously gives
entropy completeness in expectation and a shared-OPT lower bound for every
ordering of that histogram. The reference is fixed before the random word. -/
theorem exists_entropy_residual_lower_bound {n a b : Nat}
    (primary : PrefRouter Int) (depth : DepthTree a b) (base : List (Fin n))
    (primaryOrdered : primary.leaves.Pairwise (· < ·))
    (primaryKeys : ∀ key ∈ base, (key.val:Int) ∈ primary.leaves) :
    ∃ auxiliary : PrefRouter Int, auxiliary.leaves.Pairwise (· < ·) ∧
      (∀ key ∈ base, (key.val:Int) ∈ auxiliary.leaves) ∧
      (∀ requests : List (Fin n), requests.Perm base →
        residualBound primary depth auxiliary (requests.map (fun key => (key.val:Int))) ≤
          519*DynamicOptimality.OPT requests) ∧
      (base.length:ℝ)+histogramEntropyBits (base.map (fun key => (key.val:Int))) ≤
        2*(Real.log 3/Real.log 2)*shuffleExpectation (base.map (fun key => (key.val:Int)))
          (fun word => (residualBound primary depth auxiliary word:ℝ)) := by
  have covers : ∀ key ∈ base.map (fun key => (key.val:Int)), key ∈ primary.leaves := by
    intro key present
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    exact primaryKeys original member
  obtain ⟨auxiliary,ordered,keys,entropy⟩ := exists_expected_residual_entropy primary depth
    (base.map (fun key => (key.val:Int))) covers
  have auxiliaryKeys : ∀ key ∈ base, (key.val:Int) ∈ auxiliary.leaves := by
    intro key present
    exact keys _ (List.mem_map.mpr ⟨key,present,rfl⟩)
  refine ⟨auxiliary,ordered,auxiliaryKeys,?_,?_⟩
  · intro requests permuted
    exact residual_shared_OPT primary depth auxiliary requests primaryOrdered ordered
      (fun key present => primaryKeys key (permuted.mem_iff.mp present))
      (fun key present => auxiliaryKeys key (permuted.mem_iff.mp present))
  · simpa only [List.length_map] using entropy

end ChaCha.Entropy
