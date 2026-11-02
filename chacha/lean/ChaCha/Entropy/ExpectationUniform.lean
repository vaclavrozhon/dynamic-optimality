import ChaCha.Entropy.Histogram
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fintype

/-!
# A genuine uniform fixed-histogram probability space

The sample space consists of all permutations of the *occurrence indices*
of a supplied word. Equal keys remain separate tokens. Each permutation has
probability `1/m!`; reading its tokens produces the randomized request word.
The finite expectation below is exactly the sum weighted by this probability
mass function, including the unique permutation of the empty word.
-/

namespace ChaCha.Entropy

open scoped BigOperators

noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ outcome, f outcome) / (Fintype.card Ω : ℝ)

theorem uniformMean_congr {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (same : ∀ outcome, f outcome = g outcome) : uniformMean f = uniformMean g := by
  simp only [uniformMean]
  congr 1
  exact Finset.sum_congr rfl (fun outcome _ => same outcome)

theorem uniformMean_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (equivalence : Ω ≃ Γ) (f : Γ → ℝ) :
    uniformMean (fun outcome => f (equivalence outcome)) = uniformMean f := by
  simp only [uniformMean,equivalence.sum_comp,Fintype.card_congr equivalence]

@[simp] theorem uniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (value : ℝ) :
    uniformMean (fun _ : Ω => value) = value := by
  have positive : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  simp only [uniformMean,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem uniformMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun outcome => f outcome + g outcome) = uniformMean f + uniformMean g := by
  simp only [uniformMean,Finset.sum_add_distrib,add_div]

theorem uniformMean_mul {Ω : Type*} [Fintype Ω] (value : ℝ) (f : Ω → ℝ) :
    uniformMean (fun outcome => value * f outcome) = value * uniformMean f := by
  simp only [uniformMean,← Finset.mul_sum,mul_div_assoc]

theorem uniformMean_sum {Ω ι : Type*} [Fintype Ω] (indices : Finset ι) (f : ι → Ω → ℝ) :
    uniformMean (fun outcome => ∑ index ∈ indices, f index outcome) =
      ∑ index ∈ indices, uniformMean (f index) := by
  simp only [uniformMean]
  rw [Finset.sum_comm,Finset.sum_div]

theorem uniformMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (pointwise : ∀ outcome, f outcome ≤ g outcome) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun outcome _ => pointwise outcome)) (Nat.cast_nonneg _)

theorem uniformMean_nonneg {Ω : Type*} [Fintype Ω] {f : Ω → ℝ}
    (pointwise : ∀ outcome, 0 ≤ f outcome) : 0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg (fun outcome _ => pointwise outcome)) (Nat.cast_nonneg _)

/-- This identifies the finite average with an actual normalized PMF, rather
than imposing an expected-cost equation as an assumption. -/
theorem uniformMean_eq_PMF {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    uniformMean f = ∑ outcome, (PMF.uniformOfFintype Ω outcome).toReal * f outcome := by
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    uniformMean,div_eq_mul_inv,mul_comm,Finset.sum_mul]

abbrev ShuffleSample {α : Type*} (base : List α) := Equiv.Perm (Fin base.length)

noncomputable def shuffleProbability {α : Type*} (base : List α) : PMF (ShuffleSample base) :=
  PMF.uniformOfFintype _

/-- Read the original keys in a uniformly permuted order of their distinct
occurrence indices. -/
def sampleWord {α : Type*} (base : List α) (sample : ShuffleSample base) : List α :=
  List.ofFn (base.get ∘ sample)

theorem sampleWord_perm {α : Type*} (base : List α) (sample : ShuffleSample base) :
    (sampleWord base sample).Perm base := by
  simpa only [sampleWord,List.ofFn_get] using sample.ofFn_comp_perm base.get

@[simp] theorem sampleWord_length {α : Type*} (base : List α) (sample : ShuffleSample base) :
    (sampleWord base sample).length = base.length := (sampleWord_perm base sample).length_eq

theorem sampleWord_histogram {α : Type*} [DecidableEq α] (base : List α)
    (sample : ShuffleSample base) (key : α) :
    (sampleWord base sample).count key = base.count key := (sampleWord_perm base sample).count_eq key

noncomputable def shuffleExpectation {α : Type*} (base : List α) (statistic : List α → ℝ) : ℝ :=
  uniformMean (fun sample : ShuffleSample base => statistic (sampleWord base sample))

theorem shuffleExpectation_eq_PMF {α : Type*} (base : List α) (statistic : List α → ℝ) :
    shuffleExpectation base statistic =
      ∑ sample, (shuffleProbability base sample).toReal * statistic (sampleWord base sample) :=
  uniformMean_eq_PMF _

end ChaCha.Entropy
