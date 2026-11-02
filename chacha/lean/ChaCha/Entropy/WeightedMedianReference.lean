import ChaCha.Entropy.WeightedMedianAssembly

/-! # A histogram-dependent auxiliary reference certifying entropy

The reference is chosen solely from the ordered keys and their request
counts. It is independent of their random order. The estimate is in
natural-log units; dividing by log(2) gives the manuscript's bit entropy
and its coefficient log_2(3).
-/

namespace ChaCha.Entropy

open PreferredProjection

theorem exists_optional_weighted_reference (f : Int → Nat) (keys : List Int)
    (positive : ∀ key ∈ keys, 0 < f key) :
    ∃ reference : Option (PrefRouter Int), optionalLeaves reference = keys ∧
      entropyMass f keys ≤ Real.log 3*(2*optionalMass f reference+(weight f keys:ℝ)) := by
  by_cases empty : keys = []
  · subst keys
    exact ⟨none,rfl,by simp [optionalMass]⟩
  · obtain ⟨left,pivot,right,same,low,high,pivotPositive⟩ := exists_weighted_median f keys
      (weight_pos_of_nonempty f keys empty positive)
    have leftPositive : ∀ key ∈ left, 0 < f key := by
      intro key member
      apply positive key
      rw [same]
      simp [member]
    have rightPositive : ∀ key ∈ right, 0 < f key := by
      intro key member
      apply positive key
      rw [same]
      simp [member]
    obtain ⟨leftRef,leftWord,leftBound⟩ := exists_optional_weighted_reference f left leftPositive
    obtain ⟨rightRef,rightWord,rightBound⟩ := exists_optional_weighted_reference f right rightPositive
    have total : weight f keys = weight f left+f pivot+weight f right := by
      rw [same,weight_append,weight_cons]
      omega
    have word : (aroundMedian f pivot leftRef rightRef).leaves = keys := by
      rw [aroundMedian_leaves,leftWord,rightWord]
      exact same.symm
    have bound := aroundMedian_entropy f pivot leftRef rightRef pivotPositive (by
      simpa only [leftWord,rightWord,total] using low) (by
      simpa only [leftWord,rightWord,total] using high) (by
      simpa only [leftWord] using leftBound) (by
      simpa only [rightWord] using rightBound)
    exact ⟨some (aroundMedian f pivot leftRef rightRef),word,by simpa only [word,optionalMass] using bound⟩
termination_by keys.length
decreasing_by all_goals
  have lengths := congrArg List.length same
  simp only [List.length_append,List.length_cons] at lengths
  omega

theorem exists_ordered_weighted_reference (f : Int → Nat) (keys : List Int)
    (nonempty : keys ≠ []) (ordered : keys.Pairwise (· < ·))
    (positive : ∀ key ∈ keys, 0 < f key) :
    ∃ reference : PrefRouter Int, reference.leaves = keys ∧ reference.leaves.Pairwise (· < ·) ∧
      entropyMass f keys ≤ Real.log 3*(2*alternationMass f reference+(weight f keys:ℝ)) := by
  obtain ⟨reference,word,bound⟩ := exists_optional_weighted_reference f keys positive
  cases reference with
  | none => exact (nonempty word.symm).elim
  | some reference =>
    have same : reference.leaves = keys := word
    exact ⟨reference,same,by simpa only [same] using ordered,bound⟩

end ChaCha.Entropy
