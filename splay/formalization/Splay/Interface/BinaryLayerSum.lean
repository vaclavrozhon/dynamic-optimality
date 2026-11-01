import Splay.Interface.LogarithmicRowCharge

namespace Splay.Interface.BinaryLayerSum

open scoped BigOperators

/-- A finite geometric sum with a linear numerator. The unspent remainder
makes the induction independent of any convergence theorem. -/
theorem geometric_linear (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ) :
    (∑ t ∈ Finset.range N, (a * t + b) / 2 ^ t) ≤ 2 * a + 2 * b := by
  have exactSum : ∀ N : ℕ,
      (∑ t ∈ Finset.range N, (a * t + b) / 2 ^ t) +
        (2 * a * (N + 1) + 2 * b) / 2 ^ N = 2 * a + 2 * b := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [pow_succ]
      convert ih using 1 <;> ring
  have remainder : 0 ≤ (2 * a * (N + 1) + 2 * b) / (2 : ℚ) ^ N := by positivity
  linarith [exactSum N]

/-- Count rows whose integer error reaches a binary layer. Lists retain
multiplicity, so repeated pairings are counted separately. -/
def layerCount {α : Type*} (error : α → ℕ) (rows : List α) (t : ℕ) : ℕ :=
  (rows.filter fun row => decide (2 ^ t ≤ error row)).length

theorem layerCount_partition {α : Type*} (error : α → ℕ) (rows : List α)
    (early : α → Bool) (t : ℕ) :
    layerCount error rows t ≤ layerCount error (rows.filter early) t +
      (rows.filter fun row => !(early row)).length := by
  induction rows with
  | nil => simp [layerCount]
  | cons row rows ih =>
    cases h : early row <;> by_cases large : 2 ^ t ≤ error row <;>
      simp [layerCount, h, large] at ih ⊢ <;> omega

theorem layerCount_le_error {α : Type*} (error : α → ℕ) (rows : List α) (t : ℕ) :
    2 ^ t * layerCount error rows t ≤ (rows.map error).sum := by
  induction rows with
  | nil => simp [layerCount]
  | cons row rows ih =>
    by_cases large : 2 ^ t ≤ error row <;>
      simp [layerCount, large, Nat.mul_add] at ih ⊢ <;> omega

theorem charge_eq_layers {α : Type*} (error : α → ℕ) (rows : List α) :
    ∃ N : ℕ, (rows.map fun row => LogarithmicRowCharge.charge (error row)).sum =
      ∑ t ∈ Finset.range N, layerCount error rows t := by
  let N := (rows.map fun row => LogarithmicRowCharge.charge (error row)).sum
  have single (row : α) (member : row ∈ rows) :
      LogarithmicRowCharge.charge (error row) ≤ N := by
    exact List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map.mpr ⟨row, member, rfl⟩)
  have count (row : α) (member : row ∈ rows) :
      (∑ t ∈ Finset.range N, if 2 ^ t ≤ error row then 1 else 0) =
        LogarithmicRowCharge.charge (error row) := by
    have equivalence (t : ℕ) : 2 ^ t ≤ error row ↔ t < LogarithmicRowCharge.charge (error row) := by
      rw [LogarithmicRowCharge.charge, Nat.lt_clog_iff_pow_lt (by decide)]
      omega
    simp_rw [equivalence]
    rw [← Finset.sum_filter]
    have filter : (Finset.range N).filter (fun t => t < LogarithmicRowCharge.charge (error row)) =
        Finset.range (LogarithmicRowCharge.charge (error row)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      have := single row member
      omega
    simp [filter]
  refine ⟨N, ?_⟩
  have swap : ∀ rows : List α,
      (∑ t ∈ Finset.range N, layerCount error rows t) =
        (rows.map fun row => ∑ t ∈ Finset.range N, if 2 ^ t ≤ error row then 1 else 0).sum := by
    intro rows
    induction rows with
    | nil => simp [layerCount]
    | cons row rows ih =>
      have head (t : ℕ) : layerCount error (row :: rows) t =
          (if 2 ^ t ≤ error row then 1 else 0) + layerCount error rows t := by
        by_cases large : 2 ^ t ≤ error row <;> simp [layerCount, large, Nat.add_comm]
      simp_rw [head]
      rw [Finset.sum_add_distrib, ih]
      simp
  rw [swap]
  congr 1
  apply List.map_congr_left
  intro row member
  exact (count row member).symm

/-- An early error bound linear in the cutoff and an exponentially decaying
late row count imply a logarithmic-error budget with no value-cap factor. -/
theorem logarithmic_charge_bound {α : Type*}
    (error : α → ℕ) (rows : List α) (early : ℕ → α → Bool)
    (C U T : ℕ)
    (prefixBound : ∀ k, ((rows.filter (early k)).map error).sum ≤ C * (k + 1) * U)
    (tail : ∀ k, 2 ^ k * (rows.filter fun row => !(early k row)).length ≤ T)
    (k : ℕ) :
    2 ^ k * (rows.map fun row => LogarithmicRowCharge.charge (error row)).sum ≤
      2 ^ k * (2 * C * (k + 2) * U) + 2 * T := by
  have layers (t : ℕ) :
      2 ^ (k + t) * layerCount error rows t ≤
        2 ^ k * (C * (k + t + 1) * U) + T := by
    have partition := Nat.mul_le_mul_left (2 ^ (k + t))
      (layerCount_partition error rows (early (k + t)) t)
    have first := Nat.mul_le_mul_left (2 ^ k)
      ((layerCount_le_error error (rows.filter (early (k + t))) t).trans (prefixBound (k + t)))
    have last := tail (k + t)
    rw [pow_add] at partition last ⊢
    nlinarith only [partition, first, last]
  obtain ⟨N, equation⟩ := charge_eq_layers error rows
  have rational (t : ℕ) : (layerCount error rows t : ℚ) ≤
      ((C * U : ℕ) * t + ((C * (k + 1) * U : ℕ) + (T : ℚ) / 2 ^ k)) / 2 ^ t := by
    have cast : (2 : ℚ) ^ (k + t) * layerCount error rows t ≤
        (2 : ℚ) ^ k * (C * (k + t + 1) * U) + T := by exact_mod_cast layers t
    rw [pow_add] at cast
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ t)).mpr
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℚ) < 2 ^ k)).mp
    push_cast
    field_simp
    nlinarith only [cast]
  have total := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range N) => rational t)
  have geometric := geometric_linear ((C * U : ℕ) : ℚ)
    ((C * (k + 1) * U : ℕ) + (T : ℚ) / 2 ^ k) (by positivity) (by positivity) N
  have castSum : ((∑ t ∈ Finset.range N, layerCount error rows t : ℕ) : ℚ) =
      ∑ t ∈ Finset.range N, (layerCount error rows t : ℚ) := by simp
  have paid := total.trans geometric
  rw [← castSum, ← equation] at paid
  have scaled := mul_le_mul_of_nonneg_left paid (show (0 : ℚ) ≤ 2 ^ k by positivity)
  have rationalResult : (2 : ℚ) ^ k *
      (rows.map fun row => LogarithmicRowCharge.charge (error row)).sum ≤
      (2 : ℚ) ^ k * (2 * C * (k + 2) * U) + 2 * T := by
    push_cast at scaled ⊢
    field_simp at scaled
    nlinarith only [scaled]
  exact_mod_cast rationalResult

end Splay.Interface.BinaryLayerSum
