import DyadicRankCompression

namespace Splay.Interface.LogarithmicRowCharge

open Splay.Research.DyadicRankCompression

/-- Binary layers of an integer error; a zero error has zero charge. -/
def charge (error : ℕ) : ℕ := Nat.clog 2 (error + 1)

theorem label_add_log {rank : ℕ} (positive : 1 ≤ rank) (error : ℕ) :
    label (rank + error) ≤ label rank + charge error := by
  have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) rank
  have multiplier := Nat.le_pow_clog (by decide : 1 < 2) (error + 1)
  have product : rank + error ≤ rank * (error + 1) := by nlinarith
  have strict : rank + error < 2 ^ (Nat.log 2 rank + charge error + 1) := by
    calc
      rank + error ≤ rank * (error + 1) := product
      _ ≤ rank * 2 ^ charge error := Nat.mul_le_mul_left _ multiplier
      _ < 2 ^ (Nat.log 2 rank + 1) * 2 ^ charge error :=
        Nat.mul_lt_mul_of_pos_right upper (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have logs := Nat.log_lt_of_lt_pow (by omega : rank + error ≠ 0) strict
  unfold label
  omega

theorem label_le_charge {error : ℕ} (positive : 1 ≤ error) :
    label error ≤ charge error := by
  have lower := Nat.pow_log_le_self 2 (by omega : error ≠ 0)
  have logs : Nat.log 2 error < charge error :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  unfold label
  omega

/-- The positive relabeling cost is logarithmic in the historical error. -/
theorem positive_bound {winner old new error : ℕ}
    (oldPositive : 1 ≤ old) (identity : new + winner ≤ old + error) :
    label new - label old ≤ charge error := by
  have mono := label_monotone (show new ≤ old + error by omega)
  have bound := label_add_log oldPositive error
  omega

/-- The signed relabeling and pair preparation together use at most twice
the logarithmic error charge. No additive per-pair charge is introduced. -/
theorem combined_bound {winner old new error : ℕ}
    (winnerPositive : 1 ≤ winner) (oldPositive : 1 ≤ old) (newPositive : 1 ≤ new)
    (identity : new + winner ≤ old + error) :
    (label new - label old) + (label winner + 1 - label old) ≤
      (label old - label new) + 2 * charge error := by
  by_cases order : winner < old
  · have basePositive : 1 ≤ old - winner := by omega
    have preparation := zero_error_preparation winnerPositive basePositive
      (show old - winner + winner ≤ old by omega)
    have baseLabel := label_monotone (show old - winner ≤ old by omega)
    have mono := label_monotone (show new ≤ (old - winner) + error by omega)
    have logarithmic := label_add_log basePositive error
    omega
  · have errorPositive : 1 ≤ error := by omega
    have newBound := label_monotone (show new ≤ error by omega)
    have newLog := label_le_charge errorPositive
    have winnerBound := label_monotone (show winner ≤ old + error by omega)
    have winnerLog := label_add_log oldPositive error
    have oldLabel := label_positive old
    omega

end Splay.Interface.LogarithmicRowCharge
