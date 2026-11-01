import Splay.Interface.UClockCutState

namespace Splay.Interface

private theorem ClockCutOrderedAt.congr_on
    {α : Type*} {oldClock newClock : α → ℕ} {cutoff : ℕ}
    {elements : List α}
    (ordered : ClockCutOrderedAt oldClock cutoff elements)
    (same :
      ∀ element ∈ elements, newClock element = oldClock element) :
    ClockCutOrderedAt newClock cutoff elements := by
  unfold ClockCutOrderedAt at ordered ⊢
  apply ordered.imp_of_mem
  intro earlier later earlierMem laterMem relation laterHigh
  rw [same later laterMem] at laterHigh
  rw [same earlier earlierMem]
  exact relation laterHigh

private theorem ClockCutOrderedAt.sublist_congr
    {α : Type*} {oldClock newClock : α → ℕ} {cutoff : ℕ}
    {small large : List α}
    (sublist : small.Sublist large)
    (ordered : ClockCutOrderedAt oldClock cutoff large)
    (same : ∀ element ∈ small, newClock element = oldClock element) :
    ClockCutOrderedAt newClock cutoff small := by
  apply ClockCutOrderedAt.congr_on
    (List.Pairwise.sublist sublist ordered)
  exact same

private theorem ClockCutOrderedAt.cons_of_head_high
    {α : Type*} {clock : α → ℕ} {cutoff : ℕ}
    {head : α} {tail : List α}
    (headHigh : cutoff ≤ clock head)
    (tailOrdered : ClockCutOrderedAt clock cutoff tail) :
    ClockCutOrderedAt clock cutoff (head :: tail) := by
  unfold ClockCutOrderedAt at tailOrdered ⊢
  exact List.pairwise_cons.mpr
    ⟨fun _ _ _ => headHigh, tailOrdered⟩

private theorem ClockCutOrderedAt.cons_of_tail_low
    {α : Type*} {clock : α → ℕ} {cutoff : ℕ}
    {head : α} {tail : List α}
    (tailLow : ∀ element ∈ tail, clock element < cutoff)
    (tailOrdered : ClockCutOrderedAt clock cutoff tail) :
    ClockCutOrderedAt clock cutoff (head :: tail) := by
  unfold ClockCutOrderedAt at tailOrdered ⊢
  apply List.pairwise_cons.mpr
  constructor
  · intro later laterMem laterHigh
    exact False.elim <|
      (Nat.not_le_of_lt (tailLow later laterMem)) laterHigh
  · exact tailOrdered

private theorem removeLosers_sublist
    {n : ℕ} (elements : List (Element n))
    (matching : List (Pairing n)) :
    (removeLosers elements matching).Sublist elements := by
  induction matching generalizing elements with
  | nil =>
      simp [removeLosers]
  | cons pairing matching ih =>
      change
        (removeLosers (elements.erase pairing.loser) matching).Sublist
          elements
      exact (ih (elements.erase pairing.loser)).trans
        List.erase_sublist

private theorem mem_removeLosers_not_loser
    {n : ℕ} {elements : List (Element n)}
    {matching : List (Pairing n)}
    (nodup : elements.Nodup) {element : Element n}
    (member : element ∈ removeLosers elements matching) :
    element ∉ pairingLosers matching := by
  have setEq := removeLosers_toFinset elements matching nodup
  have outputMember :
      element ∈ (removeLosers elements matching).toFinset := by
    simpa using member
  rw [setEq] at outputMember
  have notMember := (Finset.mem_sdiff.mp outputMember).2
  simpa using notMember

private theorem clock_le_eventCount_of_block_mem
    {n : ℕ} {state : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)}
    (exact : EpisodeLedger.ExactAt state labels ledger)
    (clockSound : EpisodeClock.SoundAt state ledger clock events)
    {blockId : BlockId} {block : Block n} {element : Element n}
    (found : state.block? blockId = some block)
    (member : element ∈ block.elements) :
    clock element ≤ events.length := by
  obtain ⟨start, active⟩ :=
    exact.complete element
      (mem_allElements_of_block_found found member)
  exact (clockSound element start active).1

namespace StateClockCutOrderedAt

/--
The monotone position of the live episode clocks with respect to one fixed
event cut is preserved by every legal interface step.
-/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n} {ledger : EpisodeLedger n}
    {clock : EpisodeClock n} {events : List (ValueChangeEvent n)}
    {cutoff : ℕ}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (ordered : StateClockCutOrderedAt before clock cutoff)
    (step : Step params before operation after) :
    StateClockCutOrderedAt after
      (EpisodeClock.after events.length clock operation) cutoff := by
  intro query result afterFound
  unfold State.block? at afterFound
  cases step.2.1 with
  | convert sourceFound sourceGrowing blocksEq valuesEq =>
      rename_i sourceId source
      rw [blocksEq, List.getElem?_modify] at afterFound
      cases originalFound : before.blocks[query]? with
      | none =>
          simp [originalFound] at afterFound
      | some original =>
          by_cases same : sourceId = query
          · simp [originalFound, same] at afterFound
            subst result
            simpa [EpisodeClock.after] using
              ordered query original
                (by simpa [State.block?] using originalFound)
          · simp [originalFound, same] at afterFound
            subst result
            simpa [EpisodeClock.after] using
              ordered query original
                (by simpa [State.block?] using originalFound)
  | create room blocksEq valuesEq =>
      rename_i creator
      rw [blocksEq, List.getElem?_append] at afterFound
      by_cases old : query < before.blocks.length
      · simp only [old, if_pos] at afterFound
        simpa [EpisodeClock.after] using
          ordered query result
            (by simpa [State.block?] using afterFound)
      · simp only [old] at afterFound
        have offsetLt : query - before.blocks.length < 1 :=
          (List.getElem?_eq_some_iff.mp afterFound).choose
        have offsetZero : query - before.blocks.length = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offsetLt)
        simp [offsetZero] at afterFound
        subst result
        simp [EpisodeClock.after, ClockCutOrderedAt]
  | insert targetFound targetGrowing unassigned valueOrder
      blocksEq valuesEq =>
      rename_i targetId target inserted
      rw [blocksEq, List.getElem?_modify] at afterFound
      cases originalFound : before.blocks[query]? with
      | none =>
          simp [originalFound] at afterFound
      | some original =>
          have originalStateFound :
              before.block? query = some original := by
            simpa [State.block?] using originalFound
          have oldOrdered :
              ClockCutOrderedAt clock cutoff original.elements :=
            ordered query original originalStateFound
          have unchanged :
              ∀ element ∈ original.elements,
                Function.update clock inserted events.length element =
                  clock element := by
            intro element member
            have elementNe : element ≠ inserted := by
              intro same
              subst element
              exact unassigned <|
                mem_allElements_of_block_found
                  originalStateFound member
            simp [Function.update, elementNe]
          have tailOrdered :
              ClockCutOrderedAt
                (Function.update clock inserted events.length)
                cutoff original.elements :=
            oldOrdered.congr_on unchanged
          by_cases same : targetId = query
          · simp [originalFound, same] at afterFound
            subst result
            by_cases late : cutoff ≤ events.length
            · have withHead :=
                ClockCutOrderedAt.cons_of_head_high
                  (clock := Function.update clock inserted events.length)
                  (head := inserted) (tail := original.elements)
                  (by simp [Function.update, late]) tailOrdered
              simpa [EpisodeClock.after] using withHead
            · have early : events.length < cutoff :=
                Nat.lt_of_not_ge late
              have tailLow :
                  ∀ element ∈ original.elements,
                    Function.update clock inserted events.length element <
                      cutoff := by
                intro element member
                rw [unchanged element member]
                exact
                  (clock_le_eventCount_of_block_mem exact clockSound
                    originalStateFound member).trans_lt early
              have withHead :=
                ClockCutOrderedAt.cons_of_tail_low
                  (head := inserted) tailLow tailOrdered
              simpa [EpisodeClock.after] using withHead
          · simp [originalFound, same] at afterFound
            subst result
            simpa [EpisodeClock.after] using tailOrdered
  | delete sourceFound sourceShrinking present blocksEq valuesEq =>
      rename_i sourceId source deleted
      rw [blocksEq, List.getElem?_modify] at afterFound
      cases originalFound : before.blocks[query]? with
      | none =>
          simp [originalFound] at afterFound
      | some original =>
          by_cases same : sourceId = query
          · simp [originalFound, same] at afterFound
            subst result
            have oldOrdered :=
              ordered query original
                (by simpa [State.block?] using originalFound)
            exact
              ClockCutOrderedAt.sublist_congr
                List.erase_sublist oldOrdered
                (by
                  intro element member
                  rfl)
          · simp [originalFound, same] at afterFound
            subst result
            simpa [EpisodeClock.after] using
              ordered query original
                (by simpa [State.block?] using originalFound)
  | pass sourceFound validMatching blocksEq valuesEq =>
      rename_i sourceId source matching
      rw [blocksEq] at afterFound
      unfold passBlocks at afterFound
      let sourceAfter : Block n :=
        { source with
          passCount := source.passCount + 1
          elements := removeLosers source.elements matching }
      let sourceUpdated : List (Block n) :=
        before.blocks.modify sourceId fun _ => sourceAfter
      change
        (insertAtDestinations sourceUpdated matching)[query]? =
          some result at afterFound
      have sourceBlocksFound :
          before.blocks[sourceId]? = some source := by
        simpa [State.block?] using sourceFound
      have sourceNodup : source.elements.Nodup :=
        step.1.block_elements_nodup sourceFound
      have losersNodup : (pairingLosers matching).Nodup :=
        pairingLosers_nodup validMatching.2.1
      have destinationsNodup :
          (matching.map fun pairing => pairing.destination).Nodup :=
        validMatching.2.2.1
      have destinationsNeSource :
          ∀ pairing ∈ matching, pairing.destination ≠ sourceId := by
        intro pairing pairingMem
        exact (validMatching.2.2.2.1 pairing pairingMem).2.2.1
      have blockNotLoser :
          ∀ {blockId : BlockId} {block : Block n},
            before.block? blockId = some block →
            blockId ≠ sourceId →
            ∀ element ∈ block.elements,
              element ∉ pairingLosers matching := by
        intro blockId block blockFound blockNeSource
          element elementMem loserMem
        obtain ⟨pairing, pairingMem, loserEq⟩ :=
          List.mem_map.mp (by
            simpa [pairingLosers] using loserMem)
        have sourceMem : element ∈ source.elements := by
          simpa [loserEq] using
            validMatching.loser_mem pairingMem
        have idEq : blockId = sourceId :=
          step.1.blockId_eq_of_element_mem
            blockFound elementMem sourceFound sourceMem
        exact blockNeSource idEq
      by_cases destination :
          ∃ pairing ∈ matching, pairing.destination = query
      · obtain ⟨pairing, pairingMem, pairingDestination⟩ :=
          destination
        subst query
        have pairingValid :=
          validMatching.2.2.2.1 pairing pairingMem
        obtain ⟨destinationBlock, destinationFound,
            destinationGrowing, destinationCreator⟩ :=
          pairingValid.2.2.2
        have destinationBlocksFound :
            before.blocks[pairing.destination]? =
              some destinationBlock := by
          simpa [State.block?] using destinationFound
        rw [block?_insertAtDestinations_eq_of_mem
          sourceUpdated destinationsNodup pairingMem] at afterFound
        unfold sourceUpdated at afterFound
        rw [List.getElem?_modify] at afterFound
        have sourceNeDestination :
            sourceId ≠ pairing.destination :=
          Ne.symm pairingValid.2.2.1
        simp [destinationBlocksFound, sourceNeDestination] at afterFound
        subst result
        have destinationNotLoser :
            ∀ element ∈ destinationBlock.elements,
              element ∉ pairingLosers matching :=
          blockNotLoser destinationFound pairingValid.2.2.1
        have unchanged :
            ∀ element ∈ destinationBlock.elements,
              EpisodeClock.installPassStarts events.length clock matching
                  element =
                clock element := by
          intro element member
          exact
            EpisodeClock.installPassStarts_apply_of_not_mem
              events.length clock matching element
              (destinationNotLoser element member)
        have tailOrdered :
            ClockCutOrderedAt
              (EpisodeClock.installPassStarts
                events.length clock matching)
              cutoff destinationBlock.elements :=
          (ordered pairing.destination destinationBlock
              destinationFound).congr_on unchanged
        have headClock :
            EpisodeClock.installPassStarts events.length clock matching
                pairing.loser =
              events.length :=
          EpisodeClock.installPassStarts_apply_of_mem
            events.length clock losersNodup pairingMem
        by_cases late : cutoff ≤ events.length
        · have withHead :=
            ClockCutOrderedAt.cons_of_head_high
              (head := pairing.loser)
              (by simpa [headClock] using late)
              tailOrdered
          simpa [EpisodeClock.after] using withHead
        · have early : events.length < cutoff :=
            Nat.lt_of_not_ge late
          have tailLow :
              ∀ element ∈ destinationBlock.elements,
                EpisodeClock.installPassStarts
                    events.length clock matching element <
                  cutoff := by
            intro element member
            rw [unchanged element member]
            exact
              (clock_le_eventCount_of_block_mem exact clockSound
                destinationFound member).trans_lt early
          have withHead :=
            ClockCutOrderedAt.cons_of_tail_low
              (head := pairing.loser) tailLow tailOrdered
          simpa [EpisodeClock.after] using withHead
      · have queryNotDestination :
            ∀ pairing ∈ matching, pairing.destination ≠ query := by
          intro pairing pairingMem pairingDestination
          exact destination ⟨pairing, pairingMem, pairingDestination⟩
        rw [block?_insertAtDestinations_of_ne
          sourceUpdated matching query queryNotDestination] at afterFound
        unfold sourceUpdated at afterFound
        rw [List.getElem?_modify] at afterFound
        cases originalFound : before.blocks[query]? with
        | none =>
            simp [originalFound] at afterFound
        | some original =>
            have originalStateFound :
                before.block? query = some original := by
              simpa [State.block?] using originalFound
            by_cases same : sourceId = query
            · have originalEq : original = source := by
                have querySourceFound :
                    before.blocks[query]? = some source := by
                  rw [← same]
                  exact sourceBlocksFound
                rw [querySourceFound] at originalFound
                exact Option.some.inj originalFound.symm
              subst original
              simp [originalFound, same] at afterFound
              subst result
              have outputOrdered :
                  ClockCutOrderedAt
                    (EpisodeClock.installPassStarts
                      events.length clock matching)
                    cutoff
                    (removeLosers source.elements matching) := by
                apply ClockCutOrderedAt.sublist_congr
                  (removeLosers_sublist source.elements matching)
                  (ordered sourceId source sourceFound)
                intro element member
                exact
                  EpisodeClock.installPassStarts_apply_of_not_mem
                    events.length clock matching element
                    (mem_removeLosers_not_loser
                      sourceNodup member)
              simpa [EpisodeClock.after, sourceAfter] using outputOrdered
            · simp [originalFound, same] at afterFound
              subst result
              have unchanged :
                  ∀ element ∈ original.elements,
                    EpisodeClock.installPassStarts
                        events.length clock matching element =
                      clock element := by
                intro element member
                exact
                  EpisodeClock.installPassStarts_apply_of_not_mem
                    events.length clock matching element
                    (blockNotLoser originalStateFound
                      (Ne.symm same) element member)
              have outputOrdered :=
                (ordered query original originalStateFound).congr_on
                  unchanged
              simpa [EpisodeClock.after] using outputOrdered
  | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
      rename_i sourceId source prefixLength
      rw [blocksEq] at afterFound
      unfold splitBlocks at afterFound
      rw [List.getElem?_append] at afterFound
      by_cases old :
          query <
            (before.blocks.modify sourceId fun current =>
              { current with elements := [] }).length
      · simp only [old, if_pos] at afterFound
        rw [List.getElem?_modify] at afterFound
        cases originalFound : before.blocks[query]? with
        | none =>
            simp [originalFound] at afterFound
        | some original =>
            by_cases same : sourceId = query
            · simp [originalFound, same] at afterFound
              subst result
              simp [EpisodeClock.after, ClockCutOrderedAt]
            · simp [originalFound, same] at afterFound
              subst result
              simpa [EpisodeClock.after] using
                ordered query original
                  (by simpa [State.block?] using originalFound)
      · simp only [old, if_false] at afterFound
        simp only [List.length_modify] at afterFound
        have offsetLt : query - before.blocks.length < 2 :=
          (List.getElem?_eq_some_iff.mp afterFound).choose
        have offsetCases :
            query - before.blocks.length = 0 ∨
              query - before.blocks.length = 1 :=
          Nat.le_one_iff_eq_zero_or_eq_one.mp
            (Nat.le_of_lt_succ offsetLt)
        have sourceOrdered :=
          ordered sourceId source sourceFound
        rcases offsetCases with offset | offset
        · simp [offset] at afterFound
          subst result
          exact
            ClockCutOrderedAt.sublist_congr
              (List.take_sublist prefixLength source.elements)
              sourceOrdered
              (by
                intro element member
                rfl)
        · simp [offset] at afterFound
          subst result
          exact
            ClockCutOrderedAt.sublist_congr
              (List.drop_sublist prefixLength source.elements)
              sourceOrdered
              (by
                intro element member
                rfl)
  | decrease canDecrease blocksEq valuesEq =>
      simpa [EpisodeClock.after] using
        ordered query result
          (by simpa [State.block?, blocksEq] using afterFound)
  | increase canIncrease blocksEq valuesEq =>
      simpa [EpisodeClock.after] using
        ordered query result
          (by simpa [State.block?, blocksEq] using afterFound)

end StateClockCutOrderedAt

end Splay.Interface
