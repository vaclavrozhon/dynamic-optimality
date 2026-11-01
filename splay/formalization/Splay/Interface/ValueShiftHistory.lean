import Splay.Interface.WShiftHistory

namespace Splay.Interface

namespace EpisodeLedger

/--
Both values frozen by every currently open episode came from a legal state,
so they remain inside the global value range even after later value changes.
-/
def FrozenValuesBound {n : ℕ}
    (params : Parameters) (ledger : EpisodeLedger n) : Prop :=
  ∀ element start, ledger element = some start →
    start.join.valueAtJoin ≤ params.valueBound ∧
      start.creatorValueAtJoin ≤ params.valueBound

theorem frozenValuesBound_empty
    {n : ℕ} (params : Parameters) :
    FrozenValuesBound params (EpisodeLedger.empty : EpisodeLedger n) := by
  intro element start active
  simp [EpisodeLedger.empty] at active

private theorem frozenValuesBound_installPassJoins
    {n : ℕ} {params : Parameters}
    (before : State n) (labels : RootLabels) (source : BlockId)
    (matching : List (Pairing n)) (ledger : EpisodeLedger n)
    (beforeValid : before.Valid params)
    (bounded : FrozenValuesBound params ledger) :
    FrozenValuesBound params
      (EpisodeLedger.installPassJoins
        before labels source ledger matching) := by
  induction matching generalizing ledger with
  | nil =>
      exact bounded
  | cons pairing matching ih =>
      rw [EpisodeLedger.installPassJoins_cons]
      apply ih
      intro element start active
      by_cases elementEq : element = pairing.loser
      · subst element
        simp only [Function.update_self, Option.some.injEq] at active
        subst start
        constructor
        · simpa [EpisodeStart.ofJoin, makeJoinOccurrence] using
            (beforeValid.2.1 pairing.loser).2
        · simpa [EpisodeStart.ofJoin, makeJoinOccurrence] using
            (beforeValid.2.1
              (makeJoinOccurrence before labels
                (.pass source pairing.winner) pairing.loser
                pairing.destination
                pairing.winner).destinationCreator).2
      · apply bounded element start
        simpa [Function.update, elementEq] using active

/-- Frozen value bounds are preserved by every legal interface step. -/
theorem FrozenValuesBound.after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    (bounded : FrozenValuesBound params ledger)
    (step : Step params before operation after) :
    FrozenValuesBound params
      (EpisodeLedger.after before labels ledger operation) := by
  cases operation with
  | convert blockId =>
      simpa using bounded
  | create creator =>
      simpa using bounded
  | insert destination inserted =>
      intro element start active
      by_cases elementEq : element = inserted
      · subst element
        simp only [EpisodeLedger.after, Function.update_self,
          Option.some.injEq] at active
        subst start
        constructor
        · simpa [EpisodeStart.ofJoin, makeJoinOccurrence] using
            (step.1.2.1 inserted).2
        · simpa [EpisodeStart.ofJoin, makeJoinOccurrence] using
            (step.1.2.1
              (makeJoinOccurrence before labels .insert inserted
                destination inserted).destinationCreator).2
      · apply bounded element start
        simpa [EpisodeLedger.after, Function.update, elementEq] using active
  | delete source deleted =>
      intro element start active
      by_cases elementEq : element = deleted
      · subst element
        simp [EpisodeLedger.after] at active
      · apply bounded element start
        simpa [EpisodeLedger.after, Function.update, elementEq] using active
  | pass source matching =>
      exact
        frozenValuesBound_installPassJoins
          before labels source matching ledger step.1 bounded
  | split source prefixLength =>
      simpa using bounded
  | valueChange element delta =>
      simpa using bounded

end EpisodeLedger

namespace PairShiftSnapshot

/-- Every canonical snapshot of a legal lifetime pass is value-bounded. -/
theorem valuesBound_ofLifetimePass
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)} {pairing : Pairing n}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (frozen : EpisodeLedger.FrozenValuesBound params ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length)
    (pairingMem : pairing ∈ matching) :
    (ofLifetimePass exact step aligned pairingMem).ValuesBound
      params.valueBound := by
  let starts :=
    exact.pass_pairing_starts step aligned pairingMem
  have winnerBound :=
    frozen pairing.winner starts.winnerStart starts.winnerActive
  have loserBound :=
    frozen pairing.loser starts.loserStart starts.loserActive
  exact
    ⟨winnerBound.1, winnerBound.2,
      (step.1.2.1 pairing.winner).2, loserBound.2⟩

/-- Hence the complete snapshot list of one pass is pointwise bounded. -/
theorem valuesBound_lifetimePassSnapshots
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {source : BlockId}
    {matching : List (Pairing n)}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (frozen : EpisodeLedger.FrozenValuesBound params ledger)
    (step : Step params before (.pass source matching) after)
    (aligned : labels.length = before.blocks.length) :
    ∀ snapshot ∈ lifetimePassSnapshots exact step aligned,
      snapshot.ValuesBound params.valueBound := by
  intro snapshot member
  obtain ⟨attached, _attachedMem, snapshotEq⟩ :=
    List.mem_map.mp member
  subst snapshot
  exact
    valuesBound_ofLifetimePass exact frozen step aligned attached.2

end PairShiftSnapshot

namespace LifetimeHistory

/-- Frozen-value boundedness telescopes through a complete lifetime history. -/
theorem frozenValuesBound_final
    {n : ℕ} {params : Parameters}
    {initial final : State n} {initialLabels finalLabels : RootLabels}
    {initialLedger finalLedger : EpisodeLedger n}
    {operations : List (Operation n)}
    {joins : List (JoinOccurrence n)}
    {leaves : List (LeaveOccurrence n)}
    {closed : List (ClosedEpisode n)}
    (history :
      LifetimeHistory params initial initialLabels initialLedger
        operations joins leaves closed final finalLabels finalLedger)
    (bounded :
      EpisodeLedger.FrozenValuesBound params initialLedger) :
    EpisodeLedger.FrozenValuesBound params finalLedger := by
  induction history with
  | nil valid =>
      exact bounded
  | cons head tail ih =>
      exact ih (bounded.after_step head)

end LifetimeHistory

end Splay.Interface
