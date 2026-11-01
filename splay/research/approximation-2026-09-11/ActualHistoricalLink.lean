import Splay.Interface.WShiftHistory
import Mathlib.Tactic

namespace Splay.Research.ActualHistoricalLink

open Splay.Interface

def historicalRank {n : ℕ} (start : EpisodeStart n) : ℕ :=
  start.join.valueAtJoin - start.creatorValueAtJoin

theorem historicalRank_pos {n : ℕ} (start : EpisodeStart n)
    (valid : start.JoinValid) : 1 ≤ historicalRank start := by
  unfold historicalRank
  unfold EpisodeStart.JoinValid at valid
  omega

/-- Exact old-rank/new-rank arithmetic at the actual two episode starts.
The new entry is sampled before any subsequent normalization ValueChange. -/
theorem pass_identity {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (member : pairing ∈ matching) :
    let starts := exact.pass_pairing_starts step aligned member
    (((before.value pairing.loser - before.value pairing.winner : ℕ) : ℤ)) =
      (historicalRank starts.loserStart : ℤ) -
        (historicalRank starts.winnerStart : ℤ) +
        (PairShiftSnapshot.ofLifetimePass exact step aligned member).vShift -
        ((starts.loserStart.join.valueAtJoin : ℤ) - before.value pairing.loser) +
        (PairShiftSnapshot.ofLifetimePass exact step aligned member).uShift := by
  let starts := exact.pass_pairing_starts step aligned member
  have winnerValid := starts.winnerJoinValid
  have loserValid := starts.loserJoinValid
  have order : before.value pairing.winner + 1 ≤ before.value pairing.loser := by
    cases step.2.1 with
    | pass found validMatching blocks values =>
        exact (validMatching.2.2.2.1 pairing member).2.1
  change (((before.value pairing.loser - before.value pairing.winner : ℕ) : ℤ)) =
    (historicalRank starts.loserStart : ℤ) -
      (historicalRank starts.winnerStart : ℤ) +
      ((starts.winnerStart.join.valueAtJoin : ℤ) - before.value pairing.winner) -
      ((starts.loserStart.join.valueAtJoin : ℤ) - before.value pairing.loser) +
      ((starts.loserStart.creatorValueAtJoin : ℤ) - starts.winnerStart.creatorValueAtJoin)
  unfold historicalRank
  unfold EpisodeStart.JoinValid at winnerValid loserValid
  rw [Nat.cast_sub (by omega : before.value pairing.winner ≤ before.value pairing.loser),
    Nat.cast_sub (by omega : starts.loserStart.creatorValueAtJoin ≤
      starts.loserStart.join.valueAtJoin),
    Nat.cast_sub (by omega : starts.winnerStart.creatorValueAtJoin ≤
      starts.winnerStart.join.valueAtJoin)]
  ring

/-- The only loser-side contribution to a positive historical error is the
upward drift paid by `ActualLoserUpwardBudget`, with no absolute-value loss. -/
theorem error_positive_bound (winnerDrift creatorShift : ℤ)
    (loserEntry loserNow : ℕ) :
    max (winnerDrift - ((loserEntry : ℤ) - loserNow) + creatorShift) 0 ≤
      |winnerDrift| + |creatorShift| + (loserNow - loserEntry : ℕ) := by
  have winner := le_abs_self winnerDrift
  have creator := le_abs_self creatorShift
  have winnerNonnegative := abs_nonneg winnerDrift
  have creatorNonnegative := abs_nonneg creatorShift
  omega

end Splay.Research.ActualHistoricalLink
