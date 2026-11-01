import ActualRelabelRows

namespace Splay.Research.TightDyadicCompressionRanks
open Splay.Interface ActualHistoricalLabelInventory ActualRelabelRows

def RankBelowCap {n : ℕ} (params : Parameters) (ledger : EpisodeLedger n) : Prop :=
  ∀ element start, ledger element = some start → historicalRank start ≤ params.valueBound - 1

theorem empty {n : ℕ} (params : Parameters) :
    RankBelowCap params (EpisodeLedger.empty : EpisodeLedger n) := by
  intro element start active
  simp [EpisodeLedger.empty] at active

private theorem install {n : ℕ} {params : Parameters}
    (before : State n) (labels : RootLabels) (source : BlockId)
    (matching : List (Pairing n)) (ledger : EpisodeLedger n)
    (beforeValid : before.Valid params) (bounded : RankBelowCap params ledger) :
    RankBelowCap params (EpisodeLedger.installPassJoins before labels source ledger matching) := by
  induction matching generalizing ledger with
  | nil => exact bounded
  | cons pairing matching ih =>
      rw [EpisodeLedger.installPassJoins_cons]
      apply ih
      intro element start active
      by_cases same : element = pairing.loser
      · subst element
        simp only [Function.update_self, Option.some.injEq] at active
        subst start
        have upper := (beforeValid.2.1 pairing.loser).2
        have lower := (beforeValid.2.1 (makeJoinOccurrence before labels
          (.pass source pairing.winner) pairing.loser pairing.destination pairing.winner).destinationCreator).1
        change before.value pairing.loser - before.value
          (makeJoinOccurrence before labels (.pass source pairing.winner)
            pairing.loser pairing.destination pairing.winner).destinationCreator ≤ _
        omega
      · apply bounded element start
        simpa [Function.update, same] using active

theorem after_step {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (bounded : RankBelowCap params ledger) (step : Step params before operation after) :
    RankBelowCap params (EpisodeLedger.after before labels ledger operation) := by
  cases operation with
  | insert destination inserted =>
      intro element start active
      by_cases same : element = inserted
      · subst element
        simp only [EpisodeLedger.after, Function.update_self, Option.some.injEq] at active
        subst start
        have upper := (step.1.2.1 inserted).2
        have lower := (step.1.2.1
          (makeJoinOccurrence before labels .insert inserted destination inserted).destinationCreator).1
        change before.value inserted - before.value
          (makeJoinOccurrence before labels .insert inserted destination inserted).destinationCreator ≤ _
        omega
      · apply bounded element start
        simpa [EpisodeLedger.after, Function.update, same] using active
  | delete source deleted =>
      intro element start active
      by_cases same : element = deleted
      · subst element
        simp [EpisodeLedger.after] at active
      · apply bounded element start
        simpa [EpisodeLedger.after, Function.update, same] using active
  | pass source matching => exact install before labels source matching ledger step.1 bounded
  | _ => simpa using bounded

theorem pass_ranks {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels} {ledger : EpisodeLedger n}
    {source : BlockId} {matching : List (Pairing n)} {pairing : Pairing n}
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (bounded : RankBelowCap params ledger)
    (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) (member : pairing ∈ matching) :
    let timed := TimedAnnotatedPairShiftSnapshot.ofLifetimePass clock events exact step aligned member
    winnerRank timed ≤ params.valueBound - 1 ∧ oldRank timed ≤ params.valueBound - 1 ∧
      newRank timed ≤ params.valueBound - 1 := by
  let starts := exact.pass_pairing_starts step aligned member
  have winner := bounded pairing.winner starts.winnerStart starts.winnerActive
  have loser := bounded pairing.loser starts.loserStart starts.loserActive
  refine ⟨winner, loser, ?_⟩
  rw [newRank_ofLifetimePass clock events exact sound step aligned member]
  have upper := (step.1.2.1 pairing.loser).2
  have lower := (step.1.2.1 pairing.winner).1
  omega

theorem operation_ranks {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels) (ledger : EpisodeLedger n)
    (clock : EpisodeClock n) (events : List (ValueChangeEvent n))
    (operation : Operation n) (exact : EpisodeLedger.ExactAt before labels ledger)
    (bounded : RankBelowCap params ledger) (sound : EpisodeClock.SoundAt before ledger clock events)
    (step : Step params before operation after) (aligned : labels.length = before.blocks.length)
    {timed : TimedAnnotatedPairShiftSnapshot n}
    (member : timed ∈ operationTimedPairShiftSnapshots before after labels ledger clock events
      operation exact step aligned) :
    winnerRank timed ≤ params.valueBound - 1 ∧ oldRank timed ≤ params.valueBound - 1 ∧
      newRank timed ≤ params.valueBound - 1 := by
  cases operation with
  | pass source matching =>
      obtain ⟨pairing, _, pairEq⟩ := List.mem_map.mp member
      subst timed
      exact pass_ranks clock events exact bounded sound step aligned pairing.2
  | _ => simp [operationTimedPairShiftSnapshots] at member

theorem history_ranks {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n} {initialClock finalClock : EpisodeClock n}
    {initialEvents finalEvents : List (ValueChangeEvent n)} {operations : List (Operation n)}
    {snapshots : List (TimedAnnotatedPairShiftSnapshot n)}
    (history : LifetimeHistory.TimedPairShiftHistory params initial initialLabels initialLedger
      initialClock initialEvents operations snapshots final finalLabels finalLedger finalClock finalEvents)
    (bounded : RankBelowCap params initialLedger) :
    ∀ timed ∈ snapshots,
      winnerRank timed ≤ params.valueBound - 1 ∧ oldRank timed ≤ params.valueBound - 1 ∧
        newRank timed ≤ params.valueBound - 1 := by
  revert bounded
  induction history with
  | nil valid sound => simp
  | @cons before middle final beforeLabels finalLabels beforeLedger finalLedger
      beforeClock finalClock beforeEvents finalEvents operation operations tailSnapshots
      aligned exact sound head tail ih =>
      intro bounded timed member
      rcases List.mem_append.mp member with headMember | tailMember
      · exact operation_ranks before middle beforeLabels beforeLedger beforeClock beforeEvents
          operation exact bounded sound head aligned headMember
      · exact ih (after_step bounded head) timed tailMember

end Splay.Research.TightDyadicCompressionRanks

#print axioms Splay.Research.TightDyadicCompressionRanks.history_ranks
