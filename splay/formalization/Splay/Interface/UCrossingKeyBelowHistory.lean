import Splay.Interface.UAdjacentCutHistory
import Splay.Interface.URootClockCutUniqueHistory

namespace Splay.Interface

/--
Every old crossing key remains below the counter of a mixed block after one
operation.  A mixed block either inherits a mixed predecessor, where the old
floor transports monotonically, or is growing; the latter is impossible for
an already charged shrinking root.
-/
theorem old_crossingKey_below_after_operation
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {clock : EpisodeClock n} {events : List (ValueChangeEvent n)}
    {operation : Operation n}
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (step : Step params before operation after)
    {cutoff : ℕ} {past : List LineageRunKey}
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock cutoff past)
    {key : LineageRunKey} (keyMember : key ∈ past)
    {blockId : BlockId} {block : Block n}
    (blockFound : after.block? blockId = some block)
    (labelFound :
      RootLabels.root? (RootLabels.after labels operation) blockId =
        some key.1)
    (mixed :
      BlockClockMixedAt
        (EpisodeClock.after events.length clock operation)
        cutoff block) :
    key.2 < block.passCount := by
  rcases
      after_mixed_predecessor_or_growing
        aligned accumulator.ordered step blockFound labelFound mixed with
    predecessor | growing
  · obtain
      ⟨beforeId, beforeBlock, beforeFound, beforeLabel, beforeMixed,
        counterMonotone, predecessorId⟩ := predecessor
    have oldBelow :=
      accumulator.pastBelow key keyMember beforeId beforeBlock
        beforeFound beforeLabel beforeMixed
    omega
  · obtain ⟨rootBlock, rootFound, rootShrinking⟩ :=
      accumulator.pastRootsShrinking key keyMember
    obtain ⟨afterRoot, afterRootFound, afterRootShrinking⟩ :=
      RootLineagePhase.shrinking_block_after_step
        step rootFound rootShrinking
    have afterPhase := phase.after_step aligned step
    have noGrowing :=
      afterPhase.growingIsRoot.noGrowingInLineage_of_root_shrinking
        afterRootFound afterRootShrinking
    exact False.elim <|
      noGrowing blockId block blockFound labelFound growing

/--
A crossing key emitted by the current pass is strictly below every mixed
after-block of its root.  Root-cut uniqueness identifies the old mixed
predecessor with the pass source, and the exact pass effect supplies the
strict counter increment.
-/
theorem operation_crossingKey_below_after_cut
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past)
    {key : LineageRunKey}
    (keyMember :
      key ∈
        (clockCrossingTimedSnapshots eventIndex
          (operationTimedPairShiftSnapshots before after labels ledger clock
            events operation exact step aligned)).map
              TimedAnnotatedPairShiftSnapshot.uRunKey)
    {blockId : BlockId} {block : Block n}
    (blockFound : after.block? blockId = some block)
    (labelFound :
      RootLabels.root? (RootLabels.after labels operation) blockId =
        some key.1)
    (mixed :
      BlockClockMixedAt
        (EpisodeClock.after events.length clock operation)
        (eventIndex + 1) block) :
    key.2 < block.passCount := by
  cases operation with
  | convert source =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | create creator =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | insert target inserted =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | delete source deleted =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | @pass source matching =>
      obtain ⟨timed, timedMember, keyEq⟩ :=
        List.mem_map.mp keyMember
      have timedInfo := List.mem_filter.mp timedMember
      have rawMember :
          timed ∈
            timedLifetimePassSnapshots clock events exact step aligned :=
        timedInfo.1
      have crossing :
          timed.UClockStraddlesAt eventIndex := by
        simpa [clockCrossingTimedSnapshots] using timedInfo.2
      obtain
          ⟨sourceBlock, sourceFound, sourceRoot, sourceCount, sourceMixed⟩ :=
        cut_spec_of_mem_timedLifetimePassSnapshots
          clock events exact step aligned rawMember crossing
      have keyRoot :
          timed.annotated.sourceRoot = key.1 := by
        simpa [TimedAnnotatedPairShiftSnapshot.uRunKey] using
          congrArg Prod.fst keyEq
      have keyCount :
          timed.annotated.sourcePassCount = key.2 := by
        simpa [TimedAnnotatedPairShiftSnapshot.uRunKey] using
          congrArg Prod.snd keyEq
      rcases
          after_mixed_predecessor_or_growing
            aligned accumulator.ordered step blockFound labelFound mixed with
        predecessor | growing
      · obtain
          ⟨beforeId, beforeBlock, beforeFound, beforeLabel, beforeMixed,
            counterMonotone, predecessorId⟩ := predecessor
        have sameRoot :
            RootLabels.root? labels source =
              some key.1 := by
          rw [← keyRoot]
          exact sourceRoot
        have sourceEqBefore :
            source = beforeId :=
          accumulator.unique key.1 source sourceBlock beforeId beforeBlock
            sourceFound sameRoot sourceMixed
            beforeFound beforeLabel beforeMixed
        have beforeEqSource :
            beforeBlock = sourceBlock := by
          subst beforeId
          rw [sourceFound] at beforeFound
          exact Option.some.inj beforeFound.symm
        rcases predecessorId with sameId | splitId
        · have blockIdEq : blockId = source := by
            rw [← sameId, ← sourceEqBefore]
          obtain
              ⟨effectSource, afterSource, effectSourceFound,
                afterSourceFound, creatorEq, countIncrement, modeEq,
                lengthEq⟩ :=
            step.2.1.pass_decay
          have effectSourceEq : effectSource = sourceBlock := by
            rw [sourceFound] at effectSourceFound
            exact Option.some.inj effectSourceFound.symm
          subst effectSource
          rw [blockIdEq] at blockFound labelFound
          rw [afterSourceFound] at blockFound
          have blockEq : block = afterSource :=
            Option.some.inj blockFound.symm
          subst block
          rw [countIncrement, ← keyCount, ← sourceCount]
          omega
        · obtain
            ⟨splitSource, prefixLength, impossible, sourceEq,
              childPosition⟩ := splitId
          contradiction
      · obtain ⟨rootBlock, rootFound, rootShrinking⟩ :=
          operation_clockCrossing_key_root_shrinking_after
            before after labels ledger clock events (.pass source matching)
            exact step aligned phase eventIndex keyMember
        have afterPhase := phase.after_step aligned step
        have noGrowing :=
          afterPhase.growingIsRoot.noGrowingInLineage_of_root_shrinking
            rootFound rootShrinking
        exact False.elim <|
          noGrowing blockId block blockFound labelFound growing
  | split source prefixLength =>
      simp [operationTimedPairShiftSnapshots,
        clockCrossingTimedSnapshots] at keyMember
  | valueChange changed delta =>
      cases delta <;>
        simp [operationTimedPairShiftSnapshots,
          clockCrossingTimedSnapshots] at keyMember

/--
The complete pass-floor invariant is preserved and extended by one operation.
-/
theorem crossingKeyBelowCut_after_operation
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past) :
    let operationKeys :=
      (clockCrossingTimedSnapshots eventIndex
        (operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned)).map
            TimedAnnotatedPairShiftSnapshot.uRunKey
    CrossingKeyBelowCutAt after
      (RootLabels.after labels operation)
      (EpisodeClock.after events.length clock operation)
      (eventIndex + 1) (past ++ operationKeys) := by
  dsimp only
  intro key keyMember blockId block blockFound labelFound mixed
  rcases List.mem_append.mp keyMember with oldMember | newMember
  · exact
      old_crossingKey_below_after_operation
        aligned phase step accumulator oldMember
        blockFound labelFound mixed
  · exact
      operation_crossingKey_below_after_cut
        before after labels ledger clock events operation exact step aligned
        phase eventIndex past accumulator newMember
        blockFound labelFound mixed

/--
Once root-cut uniqueness for the after-state is available, the proved
pass-floor transport packages it into the exact local result consumed by the
history induction.
-/
theorem clockCutRootStepResult_of_unique_after
    {n : ℕ} {params : Parameters}
    (before after : State n) (labels : RootLabels)
    (ledger : EpisodeLedger n) (clock : EpisodeClock n)
    (events : List (ValueChangeEvent n)) (operation : Operation n)
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (step : Step params before operation after)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (eventIndex : ℕ) (past : List LineageRunKey)
    (accumulator :
      ClockCrossingAccumulatorAt before labels clock
        (eventIndex + 1) past)
    (uniqueAfter :
      RootClockCutUniqueAt after
        (RootLabels.after labels operation)
        (EpisodeClock.after events.length clock operation)
        (eventIndex + 1)) :
    let operationKeys :=
      (clockCrossingTimedSnapshots eventIndex
        (operationTimedPairShiftSnapshots before after labels ledger clock
          events operation exact step aligned)).map
            TimedAnnotatedPairShiftSnapshot.uRunKey
    ClockCutRootStepResult after
      (RootLabels.after labels operation)
      (EpisodeClock.after events.length clock operation)
      (eventIndex + 1) (past ++ operationKeys) := by
  exact
    { unique := uniqueAfter
      pastBelow :=
        crossingKeyBelowCut_after_operation
          before after labels ledger clock events operation exact step aligned
          phase eventIndex past accumulator }

end Splay.Interface
