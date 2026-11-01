import Mathlib

/-! Integer dyadic labels give sharper historical-compression constants.
No real logarithms or rounding estimates are needed. -/

namespace Splay.Research.DyadicRankCompression

def label (rank : ℕ) : ℕ := 1 + Nat.log 2 rank

theorem label_positive (rank : ℕ) : 1 ≤ label rank := by
  unfold label
  omega

theorem label_monotone {a b : ℕ} (h : a ≤ b) : label a ≤ label b := by
  have := Nat.log_mono_right (b := 2) h
  unfold label
  omega

theorem label_succ_le (rank : ℕ) : label (rank + 1) ≤ label rank + 1 := by
  by_cases h : rank = 0
  · subst rank
    norm_num [label]
  · have double : rank + 1 ≤ rank * 2 := by omega
    have mono := Nat.log_mono_right (b := 2) double
    have doubled := Nat.log_mul_base (by decide : 1 < 2) h
    unfold label
    omega

theorem label_add_le (rank change : ℕ) :
    label (rank + change) ≤ label rank + change := by
  induction change with
  | zero => simp
  | succ change ih =>
      have step := label_succ_le (rank + change)
      have bound := step.trans (Nat.add_le_add_right ih 1)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using bound

theorem label_difference_le {a b : ℕ} (order : a ≤ b) :
    label b - label a ≤ b - a := by
  have bound := label_add_le a (b - a)
  rw [Nat.add_sub_of_le order] at bound
  omega

theorem positive_relabel_bound {a old new charge : ℕ}
    (identityBound : new + a ≤ old + charge) :
    label new - label old ≤ charge := by
  have mono := label_monotone (show new ≤ old + charge by omega)
  have lipschitz := label_add_le old charge
  omega

/-- If two positive ranks lie in the same dyadic band, subtracting the
smaller from the larger goes strictly below that band. -/
theorem same_band_subtraction {a old new : ℕ}
    (winnerPositive : 1 ≤ a) (newPositive : 1 ≤ new)
    (identityBound : new + a ≤ old)
    (sameBand : label a = label old) : label new < label old := by
  have sameLog : Nat.log 2 a = Nat.log 2 old := by
    simpa [label] using sameBand
  have lower := Nat.pow_log_le_self 2 (show a ≠ 0 by omega)
  have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) old
  rw [← sameLog, pow_succ] at upper
  have below : new < 2 ^ Nat.log 2 a := by omega
  have logs := Nat.log_lt_of_lt_pow (show new ≠ 0 by omega) below
  unfold label
  omega

theorem zero_error_preparation {a old new : ℕ}
    (winnerPositive : 1 ≤ a) (newPositive : 1 ≤ new)
    (identityBound : new + a ≤ old) :
    label a + 1 - label old ≤ label old - label new := by
  have mono := label_monotone (show a ≤ old by omega)
  by_cases sameBand : label a = label old
  · have drop := same_band_subtraction winnerPositive newPositive identityBound sameBand
    omega
  · omega

theorem preparation_bound {a old new charge : ℕ}
    (winnerPositive : 1 ≤ a) (newPositive : 1 ≤ new)
    (identityBound : new + a ≤ old + charge) :
    label a + 1 - label old ≤ label old - label new + charge := by
  by_cases order : a < old
  · have mono := label_monotone (show a ≤ old by omega)
    by_cases chargeZero : charge = 0
    · subst charge
      simpa using zero_error_preparation winnerPositive newPositive identityBound
    · omega
  · have reversed : old ≤ a := by omega
    have bound := label_difference_le reversed
    have mono := label_monotone reversed
    omega

/-- The signed relabeling increase and the preparation share one error
budget. This is stronger than bounding the two costs separately. -/
theorem combined_preparation_bound {a old new charge : ℕ}
    (winnerPositive : 1 ≤ a) (newPositive : 1 ≤ new)
    (identityBound : new + a ≤ old + charge) :
    label new + (label a + 1 - label old) ≤ label old + charge := by
  by_cases order : a < old
  · have basePositive : 1 ≤ old - a := by omega
    have baseIdentity : old - a + a ≤ old := by omega
    have prep := zero_error_preparation winnerPositive basePositive baseIdentity
    have baseLabel := label_monotone (show old - a ≤ old by omega)
    have bounded : new ≤ (old - a) + charge := by omega
    have mono := label_monotone bounded
    have lipschitz := label_add_le (old - a) charge
    omega
  · have reversed : old ≤ a := by omega
    have diff := label_difference_le reversed
    have mono := label_monotone reversed
    have newLog := Nat.log_lt_self 2 (show new ≠ 0 by omega)
    have newLabel : label new ≤ new := by unfold label; omega
    have oldLabel := label_positive old
    omega

theorem combined_relabel_bound {a old new charge : ℕ}
    (winnerPositive : 1 ≤ a) (newPositive : 1 ≤ new)
    (identityBound : new + a ≤ old + charge) :
    (label new - label old) + (label a + 1 - label old) ≤
      (label old - label new) + charge := by
  have bound := combined_preparation_bound winnerPositive newPositive identityBound
  omega

/-- Any monotone positive integer labeling that pays zero-error repairs
entirely from genuine label drops needs at least the dyadic label range.
The repair multiplier is arbitrary, but finite. -/
theorem optimal_label_range (L : ℕ → ℕ) (G multiplier : ℕ)
    (capPositive : 1 ≤ G) (positive : 1 ≤ L 1) (monotone : Monotone L)
    (repair : ∀ rank, 1 ≤ rank → 2 * rank ≤ G →
      L rank + 1 - L (2 * rank) ≤ multiplier * (L (2 * rank) - L rank)) :
    label G ≤ L G := by
  have doubling : ∀ rank, 1 ≤ rank → 2 * rank ≤ G →
      L rank + 1 ≤ L (2 * rank) := by
    intro rank rankPositive bounded
    have h := repair rank rankPositive bounded
    by_contra notSeparated
    have reverse : L (2 * rank) ≤ L rank := by omega
    rw [Nat.sub_eq_zero_of_le reverse, Nat.mul_zero] at h
    omega
  have powers : ∀ k, 2 ^ k ≤ G → 1 + k ≤ L (2 ^ k) := by
    intro k
    induction k with
    | zero => intro _; simpa using positive
    | succ k ih =>
        intro bounded
        have powerPositive : 1 ≤ 2 ^ k := by
          have h : 0 < 2 ^ k := pow_pos (by decide) k
          omega
        have nextPower : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
        have previousBound : 2 ^ k ≤ G := by rw [nextPower] at bounded; omega
        have previous := ih previousBound
        have next := doubling (2 ^ k) powerPositive (by simpa [nextPower] using bounded)
        rw [nextPower]
        omega
  have powerBound := Nat.pow_log_le_self 2 (show G ≠ 0 by omega)
  have lower := powers (Nat.log 2 G) powerBound
  have larger := monotone powerBound
  unfold label
  omega

#print axioms positive_relabel_bound
#print axioms preparation_bound
#print axioms combined_relabel_bound
#print axioms optimal_label_range

end Splay.Research.DyadicRankCompression
