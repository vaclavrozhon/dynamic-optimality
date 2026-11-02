import ChaCha.Entropy.ExpectationSymmetry

/-!
# Exact switch expectation for a filtered binary word

The first local request is free. For child multiplicities `a,b`, the expected
number of switches is exactly `2ab/(a+b)`, with no startup subtraction.
Requests outside the local interval may be arbitrarily numerous.
-/

namespace ChaCha.Entropy

open scoped BigOperators
open DynamicOptimality.Funnel (descendingPairs descendingPairs_mem descendingPairs_nodup)
variable {m : Nat}

def colorCount (active : Finset (Fin m)) (label : Fin m → Bool) (side : Bool) : Nat :=
  (active.filter (fun token => label token = side)).card

theorem local_switch_sum (sample : Equiv.Perm (Fin m)) (active : Finset (Fin m))
    (label : Fin m → Bool) :
    (ChaCha.alternations ((localOrder sample active).map label) : ℝ) =
      ∑ p ∈ active, ∑ q ∈ active, if label p = label q then 0 else adjacency sample active p q := by
  let pairs := ((descendingPairs (localOrder sample active)).filter
    (fun pair => decide (label pair.1 ≠ label pair.2))).toFinset
  have contained : pairs ⊆ active ×ˢ active := by
    intro pair member
    have both := descendingPairs_mem (List.mem_filter.mp (List.mem_toFinset.mp member)).1
    exact Finset.mem_product.mpr ⟨(mem_localOrder _ _ _).mp both.1,(mem_localOrder _ _ _).mp both.2⟩
  have filtered : (active ×ˢ active).filter (fun pair => pair ∈ pairs) = pairs := by
    ext pair
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun member => ⟨contained member,member⟩⟩
  have count : pairs.card = ChaCha.alternations ((localOrder sample active).map label) := by
    rw [List.toFinset_card_of_nodup ((descendingPairs_nodup _ (localOrder_nodup sample active)).filter _)]
    exact descendingPairs_alternations label (localOrder sample active)
  have sum : (∑ p ∈ active, ∑ q ∈ active, if (p,q) ∈ pairs then (1:ℝ) else 0) = pairs.card := by
    rw [← Finset.sum_product active active (fun pair => if pair ∈ pairs then (1:ℝ) else 0)]
    simp only [Finset.sum_boole,filtered]
  rw [count] at sum
  rw [← sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases same : label p = label q <;> simp [pairs,adjacency,same]

private theorem sum_opposite (active : Finset (Fin m)) (label : Fin m → Bool) (value : ℝ) :
    (∑ p ∈ active, ∑ q ∈ active, if label p = label q then 0 else value) =
      2 * (colorCount active label false : ℝ) * (colorCount active label true : ℝ) * value := by
  have row (p : Fin m) :
      (∑ q ∈ active, if label p = label q then 0 else value) =
        if label p then (colorCount active label false : ℝ)*value
        else (colorCount active label true : ℝ)*value := by
    cases valueSide : label p <;>
      simp only [valueSide,Bool.false_eq_true,↓reduceIte,colorCount]
    · have pointwise : ∀ q, (if false = label q then 0 else value) =
          (if label q = true then (1:ℝ) else 0)*value := by intro q; cases label q <;> simp
      simp_rw [pointwise]
      rw [← Finset.sum_mul,Finset.sum_boole]
    · have pointwise : ∀ q, (if true = label q then 0 else value) =
          (if label q = false then (1:ℝ) else 0)*value := by intro q; cases label q <;> simp
      simp_rw [pointwise]
      rw [← Finset.sum_mul,Finset.sum_boole]
  simp_rw [row]
  have split : ∀ p,
      (if label p then (colorCount active label false : ℝ)*value
        else (colorCount active label true : ℝ)*value) =
      (if label p = true then (1:ℝ) else 0) * ((colorCount active label false : ℝ)*value) +
      (if label p = false then (1:ℝ) else 0) * ((colorCount active label true : ℝ)*value) := by
    intro p
    cases label p <;> simp
  simp_rw [split]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,Finset.sum_boole,Finset.sum_boole]
  change _ = 2 * (((active.filter (fun token => label token = false)).card : ℝ)) *
    (((active.filter (fun token => label token = true)).card : ℝ)) * value
  unfold colorCount
  ring

/-- Exact conditional switch expectation in one fixed interval. -/
theorem local_switch_expectation (active : Finset (Fin m)) (label : Fin m → Bool) :
    uniformMean (fun sample => (ChaCha.alternations ((localOrder sample active).map label) : ℝ)) =
      2 * (colorCount active label false : ℝ) * (colorCount active label true : ℝ) /
        (active.card : ℝ) := by
  rw [uniformMean_congr (fun sample => local_switch_sum sample active label),uniformMean_sum]
  simp_rw [uniformMean_sum]
  calc
    _ = ∑ p ∈ active, ∑ q ∈ active, if label p = label q then 0 else 1/(active.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      by_cases same : label p = label q
      · simp only [same,↓reduceIte,uniformMean_const]
      · simp only [same,↓reduceIte]
        exact adjacency_mean active hp hq (fun equal => same (congrArg label equal))
    _ = _ := by rw [sum_opposite]; ring

end ChaCha.Entropy
