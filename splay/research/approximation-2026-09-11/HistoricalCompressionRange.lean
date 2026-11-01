import HistoricalRankCompression

namespace Splay.Research.HistoricalCompressionRange

open HistoricalRankCompression

noncomputable def range (G : ℕ) : ℕ := natLabel G+1

noncomputable def logarithm (G : ℕ) : ℕ := Nat.clog 2 (range G)+1

theorem natLabel_linear (G : ℕ) : natLabel G ≤ 16*G+1 := by
  have labelBound := (label_bounds (G:ℝ)).2
  have logarithmBound := Real.log_le_sub_one_of_pos (show 0 < 1+(G:ℝ) by positivity)
  rw [← natLabel_real_cast] at labelBound
  have realBound : (natLabel G:ℝ) ≤ 16*(G:ℝ)+1 := by linarith
  exact_mod_cast realBound

theorem range_two (G : ℕ) : 2 ≤ range G := by
  have positive := natLabel_positive G
  unfold range
  omega

theorem range_linear {G : ℕ} (positive : 0 < G) : range G ≤ 18*G := by
  have bound := natLabel_linear G
  unfold range
  omega

theorem logarithm_positive (G : ℕ) : 0 < logarithm G := by
  unfold logarithm
  omega

theorem logarithm_linear {G : ℕ} (positive : 0 < G) : logarithm G ≤ 19*G := by
  have crude : Nat.clog 2 (range G) ≤ range G :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  have bound := range_linear positive
  unfold logarithm
  omega

theorem natLabel_logarithmic (G : ℕ) :
    natLabel G ≤ 16*Nat.clog 2 (G+1)+1 := by
  have powers : (1:ℝ)+(G:ℝ) ≤ (2:ℝ)^Nat.clog 2 (G+1) := by
    have bound := Nat.le_pow_clog (by decide : 1 < 2) (G+1)
    have ordered : 1+G ≤ 2^Nat.clog 2 (G+1) := by omega
    exact_mod_cast ordered
  have logBound := Real.log_le_log (show (0:ℝ) < 1+(G:ℝ) by positivity) powers
  rw [Real.log_pow] at logBound
  have logTwo : Real.log 2 ≤ 1 := by
    have bound := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at bound ⊢
    exact bound
  have rounded := (label_bounds (G:ℝ)).2
  rw [← natLabel_real_cast] at rounded
  have small : (Nat.clog 2 (G+1):ℝ)*Real.log 2 ≤ Nat.clog 2 (G+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.clog 2 (G+1))]
  have realBound : (natLabel G:ℝ) ≤ 16*(Nat.clog 2 (G+1):ℝ)+1 := by linarith
  exact_mod_cast realBound

#print axioms natLabel_logarithmic

end Splay.Research.HistoricalCompressionRange
