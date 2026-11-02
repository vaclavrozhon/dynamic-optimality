import ChaCha.Entropy.ExpectationUniform
import Mathlib.Data.List.Permutation
import Mathlib.Order.Fin.Basic

/-!
# The induced request distribution is uniform on its histogram

Occurrence permutations give every distinct request word with the same
histogram the same number of samples. This file proves that fact explicitly;
it does not merely rely on the informal interpretation of labelled tokens.
-/

namespace ChaCha.Entropy

open scoped BigOperators ENNReal

@[simp] theorem sampleWord_id (base : List Int) : sampleWord base (Equiv.refl _) = base := by
  simp only [sampleWord,Equiv.coe_refl,Function.comp_id,List.ofFn_get]

theorem sampleWord_eq_iff (base : List Int) (first second : ShuffleSample base) :
    sampleWord base first = sampleWord base second ↔
      ∀ index, base.get (first index) = base.get (second index) := by
  simp only [sampleWord,List.ofFn_inj,funext_iff,Function.comp_apply]

theorem sampleWord_base_iff (base : List Int) (sample : ShuffleSample base) :
    sampleWord base sample = base ↔ ∀ index, base.get (sample index) = base.get index := by
  simpa only [sampleWord_id,Equiv.refl_apply] using sampleWord_eq_iff base sample (Equiv.refl _)

def precomposeSamples {m : Nat} (first : Equiv.Perm (Fin m)) : Equiv.Perm (Equiv.Perm (Fin m)) where
  toFun sample := first.trans sample
  invFun sample := first.symm.trans sample
  left_inv sample := by ext index; simp
  right_inv sample := by ext index; simp

theorem precompose_fiber_iff (base : List Int) (first sample : ShuffleSample base) :
    sampleWord base (first.trans sample) = sampleWord base first ↔ sampleWord base sample = base := by
  rw [sampleWord_eq_iff,sampleWord_base_iff]
  simp only [Equiv.trans_apply]
  constructor
  · intro equal index
    simpa using equal (first.symm index)
  · intro equal index
    exact equal (first index)

def shuffleFiber (base word : List Int) : Finset (ShuffleSample base) :=
  Finset.univ.filter (fun sample => sampleWord base sample = word)

theorem shuffleFiber_same_card (base : List Int) (sample : ShuffleSample base) :
    (shuffleFiber base (sampleWord base sample)).card = (shuffleFiber base base).card := by
  let equivalence : {other : ShuffleSample base // sampleWord base other = base} ≃
      {other : ShuffleSample base // sampleWord base other = sampleWord base sample} :=
    Equiv.subtypeEquiv (precomposeSamples sample) (fun other => (precompose_fiber_iff base sample other).symm)
  have count := Fintype.card_congr equivalence
  simpa only [Fintype.card_subtype,shuffleFiber] using count.symm

theorem sampleWord_exists {base word : List Int} (permuted : word.Perm base) :
    ∃ sample : ShuffleSample base, sampleWord base sample = word := by
  let positions : Fin base.length ≃ Fin word.length :=
    (Fin.castOrderIso permuted.length_eq.symm).toEquiv
  let tokens : Fin word.length ≃ Fin base.length :=
    Equiv.ofBijective permuted.idxBij ⟨permuted.idxBij_injective,permuted.idxBij_surjective⟩
  let sample : ShuffleSample base := positions.trans tokens
  refine ⟨sample,?_⟩
  apply List.ext_getElem
  · exact (sampleWord_length base sample).trans permuted.length_eq.symm
  · intro index firstBound secondBound
    have positionEq : positions ⟨index,by simpa only [sampleWord_length] using firstBound⟩ =
        ⟨index,secondBound⟩ := rfl
    simpa only [sampleWord,List.getElem_ofFn,Function.comp_apply,sample,Equiv.trans_apply,
      tokens,Equiv.ofBijective_apply,positionEq,List.get_eq_getElem] using
      permuted.getElem_idxBij_eq_getElem ⟨index,secondBound⟩

theorem shuffleFiber_uniform {base first second : List Int}
    (firstHistogram : first.Perm base) (secondHistogram : second.Perm base) :
    (shuffleFiber base first).card = (shuffleFiber base second).card := by
  obtain ⟨firstSample,rfl⟩ := sampleWord_exists firstHistogram
  obtain ⟨secondSample,rfl⟩ := sampleWord_exists secondHistogram
  exact (shuffleFiber_same_card base firstSample).trans (shuffleFiber_same_card base secondSample).symm

/-- The distribution of the actual request word, after forgetting token
identities. Its masses are equal on the fixed-histogram class. -/
noncomputable def shuffledWordProbability (base : List Int) : PMF (List Int) :=
  (shuffleProbability base).map (sampleWord base)

theorem shuffledWordProbability_apply (base word : List Int) :
    shuffledWordProbability base word =
      (shuffleFiber base word).card / (Fintype.card (ShuffleSample base) : ℝ≥0∞) := by
  rw [shuffledWordProbability,PMF.map_apply,tsum_fintype]
  simp only [shuffleProbability,PMF.uniformOfFintype_apply]
  have summand (sample : ShuffleSample base) :
      (if word = sampleWord base sample then (Fintype.card (ShuffleSample base) : ℝ≥0∞)⁻¹ else 0) =
        (if sampleWord base sample = word then (1:ℝ≥0∞) else 0) *
          (Fintype.card (ShuffleSample base) : ℝ≥0∞)⁻¹ := by
    by_cases same : sampleWord base sample = word
    · simp [same]
    · simp [same,Ne.symm same]
  simp_rw [summand]
  rw [← Finset.sum_mul,Finset.sum_boole]
  rfl

/-- Every two request words with the prescribed histogram have exactly equal
probability under the explicit occurrence-permutation sampler. -/
theorem shuffledWordProbability_uniform {base first second : List Int}
    (firstHistogram : first.Perm base) (secondHistogram : second.Perm base) :
    shuffledWordProbability base first = shuffledWordProbability base second := by
  rw [shuffledWordProbability_apply,shuffledWordProbability_apply,
    shuffleFiber_uniform firstHistogram secondHistogram]

/-- Words outside the fixed histogram have probability zero. -/
theorem shuffledWordProbability_outside {base word : List Int} (different : ¬ word.Perm base) :
    shuffledWordProbability base word = 0 := by
  have empty : shuffleFiber base word = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro sample member
    have same := (Finset.mem_filter.mp member).2
    exact different (same ▸ sampleWord_perm base sample)
  rw [shuffledWordProbability_apply,empty]
  simp

end ChaCha.Entropy
