import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

namespace Splay.Analysis

/--
The dyadic bucket of a point gap.

For a natural-number point gap `x`, this is the exact discrete counterpart of
`⌈log₂ (x + 1)⌉`.
-/
def gapBucket (x : ℕ) : ℕ :=
  Nat.clog 2 (x + 1)

/--
The contracted point gap used in the paper, represented without real
logarithms. It is the discrete counterpart of `⌈1 + log₂ (x + 1)⌉`.
-/
def contractedGap (x : ℕ) : ℕ :=
  1 + gapBucket x

/-- The bucket is characterized by the next power of two above `x + 1`. -/
theorem gapBucket_le_iff_le_pow {x k : ℕ} :
    gapBucket x ≤ k ↔ x + 1 ≤ 2 ^ k := by
  exact Nat.clog_le_iff_le_pow (by omega)

/-- Contracting a smaller point gap cannot produce a larger value. -/
theorem contractedGap_mono : Monotone contractedGap := by
  intro x y hxy
  unfold contractedGap gapBucket
  exact Nat.add_le_add_left (Nat.clog_mono_right 2 (Nat.add_le_add_right hxy 1)) 1

/-- The unique point gap in the bottom contracted bucket is zero. -/
@[simp]
theorem contractedGap_eq_one_iff {x : ℕ} :
    contractedGap x = 1 ↔ x = 0 := by
  constructor
  · intro contracted
    have bucketZero : gapBucket x = 0 := by
      unfold contractedGap at contracted
      omega
    have upper : x + 1 ≤ 2 ^ 0 := by
      rw [← gapBucket_le_iff_le_pow]
      omega
    simp only [Nat.pow_zero] at upper
    omega
  · rintro rfl
    simp [contractedGap, gapBucket]

/-- Equal contracted values at two strictly ordered point gaps are large
enough to permit the article's temporary unit decrease of the winner. -/
theorem one_lt_contractedGap_of_lt_of_eq {winner loser : ℕ}
    (hOrder : winner < loser)
    (hEqual : contractedGap winner = contractedGap loser) :
    1 < contractedGap winner := by
  by_contra notLarge
  have winnerLower : 1 ≤ contractedGap winner := by
    unfold contractedGap
    omega
  have winnerOne : contractedGap winner = 1 := by
    omega
  have loserOne : contractedGap loser = 1 := by
    rw [← hEqual]
    exact winnerOne
  rw [contractedGap_eq_one_iff] at winnerOne loserOne
  omega

/--
The non-strict part of `lemma:internal-pairings-gap`: subtracting the winner's
point gap cannot increase the loser's contracted point gap.
-/
theorem internalPairingGap_nonincreasing (winner loser : ℕ) :
    contractedGap (loser - winner) ≤ contractedGap loser :=
  contractedGap_mono (Nat.sub_le loser winner)

/--
The strict part of `lemma:internal-pairings-gap`: if the winner and loser are
in the same dyadic bucket and the loser has the larger point gap, then after
subtracting the winner's point gap the loser's contracted point gap drops.
-/
theorem internalPairingGap_strict {winner loser : ℕ}
    (hOrder : winner < loser)
    (hGood : contractedGap winner = contractedGap loser) :
    contractedGap (loser - winner) < contractedGap loser := by
  have hBuckets : gapBucket winner = gapBucket loser := by
    unfold contractedGap at hGood
    omega

  have hLoserBucketPos : 0 < gapBucket loser := by
    unfold gapBucket
    exact Nat.clog_pos (by omega) (by omega)

  have hWinnerBucketPos : 0 < gapBucket winner := by
    rw [hBuckets]
    exact hLoserBucketPos

  have hWinnerPos : 0 < winner := by
    by_contra h
    have hWinnerZero : winner = 0 := Nat.eq_zero_of_not_pos h
    subst winner
    simp [gapBucket] at hWinnerBucketPos

  have hLower :
      2 ^ (gapBucket winner).pred < winner + 1 := by
    unfold gapBucket
    exact Nat.pow_pred_clog_lt_self (by omega) (by omega)

  have hUpper :
      loser + 1 ≤ 2 ^ gapBucket loser := by
    unfold gapBucket
    exact Nat.le_pow_clog (by omega) (loser + 1)

  generalize hk : gapBucket loser = k at hLoserBucketPos hUpper ⊢
  rw [hBuckets, hk] at hLower
  cases k with
  | zero =>
      omega
  | succ k =>
      simp only [Nat.pred_succ] at hLower
      rw [Nat.pow_succ] at hUpper
      have hDifference : loser - winner + 1 ≤ 2 ^ k := by
        omega
      have hDifferenceBucket : gapBucket (loser - winner) ≤ k := by
        rw [gapBucket_le_iff_le_pow]
        exact hDifference
      unfold contractedGap
      omega

/--
Arithmetic form of `lemma:internal-pairings-gap` from `setup.tex`.

The structural part of the later formalization will establish
`loserAfter = loserBefore - winner`; this theorem performs the entire
contracted-gap argument from that identity.
-/
theorem internalPairingGap {winner loserBefore loserAfter : ℕ}
    (hOrder : winner < loserBefore)
    (hAfter : loserAfter = loserBefore - winner) :
    contractedGap loserAfter ≤ contractedGap loserBefore ∧
      (contractedGap winner = contractedGap loserBefore →
        contractedGap loserAfter + 1 ≤ contractedGap loserBefore) := by
  subst loserAfter
  constructor
  · exact internalPairingGap_nonincreasing winner loserBefore
  · intro hGood
    exact internalPairingGap_strict hOrder hGood

/--
Subtracting the same heap-parent rank and lazy-interval gap from two ranks
commutes with taking their difference, provided both point gaps are genuine
natural-number differences.
-/
theorem internalPairingPointGap_identity
    {ownerRank winnerRank loserRank intervalGap : ℕ}
    (hPointGapDefined : ownerRank + intervalGap ≤ winnerRank)
    (hRankOrder : winnerRank < loserRank) :
    loserRank - winnerRank =
      (loserRank - ownerRank - intervalGap) -
        (winnerRank - ownerRank - intervalGap) := by
  omega

/--
`lemma:internal-pairings-gap` expressed directly in the ranks and interval gap
from the paper.

Before the pairing, both heap-children subtract the same owner rank and lazy
interval gap. Afterwards the loser is placed in a growing interval of the
winner, whose interval gap is zero.
-/
theorem internalPairingGap_of_ranks
    {ownerRank winnerRank loserRank intervalGap : ℕ}
    (hPointGapDefined : ownerRank + intervalGap ≤ winnerRank)
    (hRankOrder : winnerRank < loserRank) :
    let winnerBefore := winnerRank - ownerRank - intervalGap
    let loserBefore := loserRank - ownerRank - intervalGap
    let loserAfter := loserRank - winnerRank
    contractedGap loserAfter ≤ contractedGap loserBefore ∧
      (contractedGap winnerBefore = contractedGap loserBefore →
        contractedGap loserAfter + 1 ≤ contractedGap loserBefore) := by
  dsimp
  have hPointGapOrder :
      winnerRank - ownerRank - intervalGap <
        loserRank - ownerRank - intervalGap := by
    omega
  apply internalPairingGap hPointGapOrder
  exact internalPairingPointGap_identity hPointGapDefined hRankOrder

end Splay.Analysis
