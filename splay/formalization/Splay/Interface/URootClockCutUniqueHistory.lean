import Splay.Interface.UClockCutStateHistory
import Splay.Interface.RootLineagePhase

namespace Splay.Interface

private theorem BlockClockMixedAt.congr_on
    {n : ℕ} {oldClock newClock : EpisodeClock n} {cutoff : ℕ}
    {block : Block n}
    (mixed : BlockClockMixedAt newClock cutoff block)
    (same :
      ∀ element ∈ block.elements,
        newClock element = oldClock element) :
    BlockClockMixedAt oldClock cutoff block := by
  obtain ⟨first, second, adjacent, straddles⟩ := mixed
  have firstMem : first ∈ block.elements := by
    obtain ⟨front, back, ordered | reversed⟩ := adjacent
    · rw [ordered]
      simp
    · rw [reversed]
      simp
  have secondMem : second ∈ block.elements := by
    obtain ⟨front, back, ordered | reversed⟩ := adjacent
    · rw [ordered]
      simp
    · rw [reversed]
      simp
  refine ⟨first, second, adjacent, ?_⟩
  simpa [ClockStraddlesAt, same first firstMem, same second secondMem] using
    straddles

private theorem exists_adjacent_clockStraddles_of_ordered
    {α : Type*} {clock : α → ℕ} {cutoff : ℕ} :
    ∀ {xs : List α},
      ClockCutOrderedAt clock cutoff xs →
      (∃ high ∈ xs, cutoff ≤ clock high) →
      (∃ low ∈ xs, clock low < cutoff) →
      ∃ first second,
        Adjacent xs first second ∧
          ClockStraddlesAt clock cutoff first second := by
  intro xs ordered highExists lowExists
  induction xs with
  | nil =>
      simp at highExists
  | cons head tail ih =>
      cases tail with
      | nil =>
          obtain ⟨high, highMem, highSide⟩ := highExists
          obtain ⟨low, lowMem, lowSide⟩ := lowExists
          simp only [List.mem_singleton] at highMem lowMem
          subst high
          subst low
          omega
      | cons next rest =>
          have orderedParts :
              (∀ later ∈ next :: rest,
                cutoff ≤ clock later → cutoff ≤ clock head) ∧
                ClockCutOrderedAt clock cutoff (next :: rest) := by
            simpa [ClockCutOrderedAt] using
              (List.pairwise_cons.mp ordered)
          by_cases headHigh : cutoff ≤ clock head
          · by_cases nextHigh : cutoff ≤ clock next
            · have tailLow :
                  ∃ low ∈ next :: rest, clock low < cutoff := by
                obtain ⟨low, lowMem, lowSide⟩ := lowExists
                rcases List.mem_cons.mp lowMem with lowHead | lowTail
                · subst low
                  omega
                · exact ⟨low, lowTail, lowSide⟩
              obtain ⟨first, second, tailAdjacent, straddles⟩ :=
                ih orderedParts.2
                  ⟨next, by simp, nextHigh⟩ tailLow
              obtain ⟨front, back, direct | reverse⟩ := tailAdjacent
              · exact
                  ⟨first, second,
                    ⟨head :: front, back, Or.inl (by simp [direct])⟩,
                    straddles⟩
              · exact
                  ⟨first, second,
                    ⟨head :: front, back, Or.inr (by simp [reverse])⟩,
                    straddles⟩
            · have nextLow : clock next < cutoff :=
                Nat.lt_of_not_ge nextHigh
              refine ⟨head, next, ?_, ?_⟩
              · exact ⟨[], rest, by simp⟩
              · exact Or.inl ⟨headHigh, nextLow⟩
          · obtain ⟨high, highMem, highSide⟩ := highExists
            rcases List.mem_cons.mp highMem with highHead | highTail
            · subst high
              exact False.elim (headHigh highSide)
            · exact False.elim <|
                headHigh (orderedParts.1 high highTail highSide)

private theorem BlockClockMixedAt.of_sublist
    {n : ℕ} {clock : EpisodeClock n} {cutoff : ℕ}
    {small large : Block n}
    (sublist : small.elements.Sublist large.elements)
    (ordered : ClockCutOrderedAt clock cutoff large.elements)
    (mixed : BlockClockMixedAt clock cutoff small) :
    BlockClockMixedAt clock cutoff large := by
  obtain ⟨first, second, adjacent, straddles⟩ := mixed
  have firstSmall : first ∈ small.elements := by
    obtain ⟨front, back, direct | reverse⟩ := adjacent
    · rw [direct]
      simp
    · rw [reverse]
      simp
  have secondSmall : second ∈ small.elements := by
    obtain ⟨front, back, direct | reverse⟩ := adjacent
    · rw [direct]
      simp
    · rw [reverse]
      simp
  have firstLarge := sublist.subset firstSmall
  have secondLarge := sublist.subset secondSmall
  rcases straddles with firstHigh | secondHigh
  · obtain ⟨high, low, largeAdjacent, largeStraddles⟩ :=
      exists_adjacent_clockStraddles_of_ordered ordered
        ⟨first, firstLarge, firstHigh.1⟩
        ⟨second, secondLarge, firstHigh.2⟩
    exact ⟨high, low, largeAdjacent, largeStraddles⟩
  · obtain ⟨high, low, largeAdjacent, largeStraddles⟩ :=
      exists_adjacent_clockStraddles_of_ordered ordered
        ⟨second, secondLarge, secondHigh.1⟩
        ⟨first, firstLarge, secondHigh.2⟩
    exact ⟨high, low, largeAdjacent, largeStraddles⟩

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
      exact
        (ih (elements.erase pairing.loser)).trans List.erase_sublist

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

private theorem Adjacent.append_right
    {α : Type*} {xs ys : List α} {first second : α}
    (adjacent : Adjacent xs first second) :
    Adjacent (xs ++ ys) first second := by
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · exact
      ⟨front, back ++ ys, Or.inl (by simp [direct, List.append_assoc])⟩
  · exact
      ⟨front, back ++ ys, Or.inr (by simp [reverse, List.append_assoc])⟩

private theorem Adjacent.append_left
    {α : Type*} {xs ys : List α} {first second : α}
    (adjacent : Adjacent ys first second) :
    Adjacent (xs ++ ys) first second := by
  obtain ⟨front, back, direct | reverse⟩ := adjacent
  · exact
      ⟨xs ++ front, back, Or.inl (by simp [direct, List.append_assoc])⟩
  · exact
      ⟨xs ++ front, back, Or.inr (by simp [reverse, List.append_assoc])⟩

private theorem not_mixed_take_and_drop
    {n : ℕ} {clock : EpisodeClock n} {cutoff prefixLength : ℕ}
    {block : Block n}
    (nodup : block.elements.Nodup)
    (ordered : ClockCutOrderedAt clock cutoff block.elements) :
    ¬ (BlockClockMixedAt clock cutoff
          { block with
            elements := block.elements.take prefixLength } ∧
        BlockClockMixedAt clock cutoff
          { block with
            elements := block.elements.drop prefixLength }) := by
  rintro ⟨leftMixed, rightMixed⟩
  obtain ⟨leftFirst, leftSecond, leftAdjacent, leftStraddles⟩ :=
    leftMixed
  obtain ⟨rightFirst, rightSecond, rightAdjacent, rightStraddles⟩ :=
    rightMixed
  change
    Adjacent (block.elements.take prefixLength)
      leftFirst leftSecond at leftAdjacent
  change
    Adjacent (block.elements.drop prefixLength)
      rightFirst rightSecond at rightAdjacent
  have sourceEq :
      block.elements.take prefixLength ++
          block.elements.drop prefixLength =
        block.elements :=
    List.take_append_drop prefixLength block.elements
  have leftSourceAdjacent :
      Adjacent block.elements leftFirst leftSecond := by
    rw [← sourceEq]
    exact leftAdjacent.append_right
  have rightSourceAdjacent :
      Adjacent block.elements rightFirst rightSecond := by
    rw [← sourceEq]
    exact rightAdjacent.append_left
  have boundaryEq :=
    adjacent_clockStraddles_unique ordered
      leftSourceAdjacent leftStraddles
      rightSourceAdjacent rightStraddles
  have splitNodup :
      (block.elements.take prefixLength ++
        block.elements.drop prefixLength).Nodup := by
    rw [sourceEq]
    exact nodup
  have crossDistinct :=
    (List.nodup_append.mp splitNodup).2.2
  have leftFirstMem : leftFirst ∈ block.elements.take prefixLength := by
    obtain ⟨front, back, direct | reverse⟩ := leftAdjacent
    · rw [direct]
      simp
    · rw [reverse]
      simp
  have rightFirstMem : rightFirst ∈ block.elements.drop prefixLength := by
    obtain ⟨front, back, direct | reverse⟩ := rightAdjacent
    · rw [direct]
      simp
    · rw [reverse]
      simp
  have rightSecondMem : rightSecond ∈ block.elements.drop prefixLength := by
    obtain ⟨front, back, direct | reverse⟩ := rightAdjacent
    · rw [direct]
      simp
    · rw [reverse]
      simp
  rcases boundaryEq with direct | reverse
  · exact
      (crossDistinct leftFirst leftFirstMem
        rightFirst rightFirstMem) direct.1
  · exact
      (crossDistinct leftFirst leftFirstMem
        rightSecond rightSecondMem) reverse.1

/--
A mixed block after one legal operation is either still represented by a
mixed block of the same lineage before the operation, with no larger old pass
counter, or it is a growing block.

The predecessor identifier is unchanged except for `split`, whose two fresh
children both have the split source as predecessor.  This public
classification is also the bridge used by the pass-floor history invariant.
-/
theorem after_mixed_predecessor_or_growing
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {clock : EpisodeClock n} {events : List (ValueChangeEvent n)}
    {operation : Operation n} {cutoff : ℕ}
    (aligned : labels.length = before.blocks.length)
    (ordered : StateClockCutOrderedAt before clock cutoff)
    (step : Step params before operation after)
    {blockId root : RootId} {block : Block n}
    (blockFound : after.block? blockId = some block)
    (labelFound :
      RootLabels.root? (RootLabels.after labels operation) blockId =
        some root)
    (mixed :
      BlockClockMixedAt
        (EpisodeClock.after events.length clock operation)
        cutoff block) :
    (∃ beforeId beforeBlock,
      before.block? beforeId = some beforeBlock ∧
        RootLabels.root? labels beforeId = some root ∧
        BlockClockMixedAt clock cutoff beforeBlock ∧
        beforeBlock.passCount ≤ block.passCount ∧
        (beforeId = blockId ∨
          ∃ source prefixLength,
            operation = .split source prefixLength ∧
              beforeId = source ∧
              (blockId = before.blocks.length ∨
                blockId = before.blocks.length + 1))) ∨
      block.mode = .growing := by
  cases operation with
  | convert sourceId =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      cases step.2.1 with
      | convert sourceFound sourceGrowing blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq, List.getElem?_modify] at blockFound
          cases originalFound : before.blocks[blockId]? with
          | none =>
              simp [originalFound] at blockFound
          | some original =>
              by_cases same : sourceId = blockId
              · simp [originalFound, same] at blockFound
                subst block
                refine Or.inl ⟨blockId, original, ?_, labelBefore, ?_, ?_,
                  Or.inl rfl⟩
                · simpa [State.block?] using originalFound
                · simpa [EpisodeClock.after, BlockClockMixedAt] using mixed
                · simp
              · simp [originalFound, same] at blockFound
                subst block
                refine Or.inl ⟨blockId, original, ?_, labelBefore, ?_, ?_,
                  Or.inl rfl⟩
                · simpa [State.block?] using originalFound
                · simpa [EpisodeClock.after] using mixed
                · simp
  | create creator =>
      cases step.2.1 with
      | create room blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq, List.getElem?_append] at blockFound
          by_cases old : blockId < before.blocks.length
          · simp only [old, if_pos] at blockFound
            have oldLabelLt : blockId < labels.length := by
              simpa [aligned] using old
            have labelBefore :
                RootLabels.root? labels blockId = some root := by
              simpa [RootLabels.after, RootLabels.root?,
                List.getElem?_append_left oldLabelLt] using labelFound
            refine Or.inl ⟨blockId, block, ?_, labelBefore, ?_, ?_,
              Or.inl rfl⟩
            · simpa [State.block?] using blockFound
            · simpa [EpisodeClock.after] using mixed
            · simp
          · simp only [old, if_false] at blockFound
            have offsetLt :
                blockId - before.blocks.length < 1 :=
              (List.getElem?_eq_some_iff.mp blockFound).1
            have offsetZero :
                blockId - before.blocks.length = 0 :=
              Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offsetLt)
            simp [offsetZero] at blockFound
            subst block
            exact False.elim <| mixed.elements_ne_nil rfl
  | insert target inserted =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      cases step.2.1 with
      | insert targetFound targetGrowing unassigned valueOrder
          blocksEq valuesEq =>
          rename_i targetBlock
          unfold State.block? at blockFound
          rw [blocksEq, List.getElem?_modify] at blockFound
          cases originalFound : before.blocks[blockId]? with
          | none =>
              simp [originalFound] at blockFound
          | some original =>
              by_cases same : target = blockId
              · simp [originalFound, same] at blockFound
                subst block
                have originalEq : original = targetBlock := by
                  have targetAtBlock :
                      before.blocks[blockId]? = some targetBlock := by
                    simpa [State.block?, same] using targetFound
                  rw [originalFound] at targetAtBlock
                  exact Option.some.inj targetAtBlock
                subst original
                exact Or.inr targetGrowing
              · simp [originalFound, same] at blockFound
                subst block
                have originalStateFound :
                    before.block? blockId = some original := by
                  simpa [State.block?] using originalFound
                have insertedNotMem :
                    inserted ∉ original.elements := by
                  intro member
                  exact unassigned <|
                    mem_allElements_of_block_found
                      originalStateFound member
                have oldMixed :
                    BlockClockMixedAt clock cutoff original := by
                  apply BlockClockMixedAt.congr_on mixed
                  intro element member
                  simp [EpisodeClock.after, Function.update,
                    ne_of_mem_of_not_mem member insertedNotMem]
                exact
                  Or.inl ⟨blockId, original, originalStateFound,
                    labelBefore, oldMixed, by simp, Or.inl rfl⟩
  | delete source deleted =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      cases step.2.1 with
      | delete sourceFound sourceShrinking present blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq, List.getElem?_modify] at blockFound
          cases originalFound : before.blocks[blockId]? with
          | none =>
              simp [originalFound] at blockFound
          | some original =>
              have originalStateFound :
                  before.block? blockId = some original := by
                simpa [State.block?] using originalFound
              by_cases same : source = blockId
              · simp [originalFound, same] at blockFound
                subst block
                have oldMixed :
                    BlockClockMixedAt clock cutoff original := by
                  apply BlockClockMixedAt.of_sublist
                    (small :=
                      { original with
                        elements := original.elements.erase deleted })
                    (large := original)
                  · exact List.erase_sublist
                  · exact ordered blockId original originalStateFound
                  · simpa [EpisodeClock.after] using mixed
                exact
                  Or.inl ⟨blockId, original, originalStateFound,
                    labelBefore, oldMixed, by simp, Or.inl rfl⟩
              · simp [originalFound, same] at blockFound
                subst block
                exact
                  Or.inl ⟨blockId, original, originalStateFound,
                    labelBefore, by simpa [EpisodeClock.after] using mixed,
                    by simp, Or.inl rfl⟩
  | pass source matching =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      cases step.2.1 with
      | pass sourceFound validMatching blocksEq valuesEq =>
          rename_i sourceBlock
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          unfold passBlocks at blockFound
          let sourceAfter : Block n :=
            { sourceBlock with
              passCount := sourceBlock.passCount + 1
              elements := removeLosers sourceBlock.elements matching }
          let sourceUpdated : List (Block n) :=
            before.blocks.modify source fun _ => sourceAfter
          change
            (insertAtDestinations sourceUpdated matching)[blockId]? =
              some block at blockFound
          have sourceBlocksFound :
              before.blocks[source]? = some sourceBlock := by
            simpa [State.block?] using sourceFound
          have sourceNodup : sourceBlock.elements.Nodup :=
            step.1.block_elements_nodup sourceFound
          have destinationsNodup :
              (matching.map fun pairing => pairing.destination).Nodup :=
            validMatching.2.2.1
          have blockNotLoser :
              ∀ {query : BlockId} {original : Block n},
                before.block? query = some original →
                query ≠ source →
                ∀ element ∈ original.elements,
                  element ∉ pairingLosers matching := by
            intro query original originalFound queryNeSource
              element elementMem loserMem
            obtain ⟨pairing, pairingMem, loserEq⟩ :=
              List.mem_map.mp (by
                simpa [pairingLosers] using loserMem)
            have sourceMem : element ∈ sourceBlock.elements := by
              simpa [loserEq] using
                validMatching.loser_mem pairingMem
            have idEq : query = source :=
              step.1.blockId_eq_of_element_mem
                originalFound elementMem sourceFound sourceMem
            exact queryNeSource idEq
          by_cases destination :
              ∃ pairing ∈ matching, pairing.destination = blockId
          · obtain ⟨pairing, pairingMem, pairingDestination⟩ :=
              destination
            subst blockId
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
              sourceUpdated destinationsNodup pairingMem] at blockFound
            unfold sourceUpdated at blockFound
            rw [List.getElem?_modify] at blockFound
            have sourceNeDestination :
                source ≠ pairing.destination :=
              Ne.symm pairingValid.2.2.1
            simp [destinationBlocksFound, sourceNeDestination] at blockFound
            subst block
            exact Or.inr destinationGrowing
          · have queryNotDestination :
                ∀ pairing ∈ matching,
                  pairing.destination ≠ blockId := by
              intro pairing pairingMem pairingDestination
              exact destination
                ⟨pairing, pairingMem, pairingDestination⟩
            rw [block?_insertAtDestinations_of_ne
              sourceUpdated matching blockId queryNotDestination] at blockFound
            unfold sourceUpdated at blockFound
            rw [List.getElem?_modify] at blockFound
            cases originalFound : before.blocks[blockId]? with
            | none =>
                simp [originalFound] at blockFound
            | some original =>
                have originalStateFound :
                    before.block? blockId = some original := by
                  simpa [State.block?] using originalFound
                by_cases same : source = blockId
                · have originalEq : original = sourceBlock := by
                    have sourceAtQuery :
                        before.blocks[blockId]? = some sourceBlock := by
                      rw [← same]
                      exact sourceBlocksFound
                    rw [sourceAtQuery] at originalFound
                    exact Option.some.inj originalFound.symm
                  subst original
                  simp [originalFound, same] at blockFound
                  subst block
                  have sameClock :
                      ∀ element ∈
                          removeLosers sourceBlock.elements matching,
                        EpisodeClock.installPassStarts
                            events.length clock matching element =
                          clock element := by
                    intro element member
                    exact
                      EpisodeClock.installPassStarts_apply_of_not_mem
                        events.length clock matching element
                        (mem_removeLosers_not_loser sourceNodup member)
                  have smallMixed :
                      BlockClockMixedAt clock cutoff
                        { sourceBlock with
                          passCount := sourceBlock.passCount + 1
                          elements :=
                            removeLosers sourceBlock.elements matching } := by
                    apply BlockClockMixedAt.congr_on mixed
                    simpa [EpisodeClock.after] using sameClock
                  have oldMixed :
                      BlockClockMixedAt clock cutoff sourceBlock := by
                    apply BlockClockMixedAt.of_sublist
                      (small :=
                        { sourceBlock with
                          passCount := sourceBlock.passCount + 1
                          elements :=
                            removeLosers sourceBlock.elements matching })
                      (large := sourceBlock)
                    · exact
                        removeLosers_sublist sourceBlock.elements matching
                    · exact ordered source sourceBlock sourceFound
                    · exact smallMixed
                  exact
                    Or.inl ⟨source, sourceBlock, sourceFound,
                      (by simpa [same] using labelBefore), oldMixed,
                      by simp [sourceAfter], Or.inl same⟩
                · simp [originalFound, same] at blockFound
                  subst block
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
                  have oldMixed :
                      BlockClockMixedAt clock cutoff original := by
                    apply BlockClockMixedAt.congr_on mixed
                    simpa [EpisodeClock.after] using unchanged
                  exact
                    Or.inl ⟨blockId, original, originalStateFound,
                      labelBefore, oldMixed, by simp, Or.inl rfl⟩
  | split source prefixLength =>
      cases step.2.1 with
      | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
          rename_i sourceBlock
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          unfold splitBlocks at blockFound
          rw [List.getElem?_append] at blockFound
          by_cases old :
              blockId <
                (before.blocks.modify source fun current =>
                  { current with elements := [] }).length
          · simp only [old, if_pos] at blockFound
            have oldLabelLt : blockId < labels.length := by
              simpa [aligned] using old
            have labelBefore :
                RootLabels.root? labels blockId = some root := by
              simpa [RootLabels.after, RootLabels.root?,
                List.getElem?_append_left oldLabelLt] using labelFound
            rw [List.getElem?_modify] at blockFound
            cases originalFound : before.blocks[blockId]? with
            | none =>
                simp [originalFound] at blockFound
            | some original =>
                have originalStateFound :
                    before.block? blockId = some original := by
                  simpa [State.block?] using originalFound
                by_cases same : source = blockId
                · simp [originalFound, same] at blockFound
                  subst block
                  exact False.elim <| mixed.elements_ne_nil rfl
                · simp [originalFound, same] at blockFound
                  subst block
                  exact
                    Or.inl ⟨blockId, original, originalStateFound,
                      labelBefore,
                      by simpa [EpisodeClock.after] using mixed,
                      by simp, Or.inl rfl⟩
          · simp only [old, if_false] at blockFound
            simp only [List.length_modify] at blockFound
            obtain ⟨sourceRoot, sourceRootFound⟩ :=
              (HistoryStep.mk step rfl).split_source_root_exists aligned
            have sourceLabel : sourceRoot = root := by
              have offsetLt :
                  blockId - before.blocks.length < 2 :=
                (List.getElem?_eq_some_iff.mp blockFound).1
              have sourceLe : before.blocks.length ≤ blockId :=
                Nat.le_of_not_gt (by
                  simpa using old)
              rcases
                  Nat.le_one_iff_eq_zero_or_eq_one.mp
                    (Nat.le_of_lt_succ offsetLt) with
                offset | offset
              · have blockIdEq :
                    blockId = before.blocks.length := by
                  calc
                    blockId =
                        (blockId - before.blocks.length) +
                          before.blocks.length :=
                      (Nat.sub_add_cancel sourceLe).symm
                    _ = before.blocks.length := by simp [offset]
                subst blockId
                have copied :=
                  RootLabels.split_left_root?
                    (n := n) labels source prefixLength
                rw [sourceRootFound] at copied
                rw [← aligned] at labelFound
                rw [copied] at labelFound
                exact Option.some.inj labelFound
              · have blockIdEq :
                    blockId = before.blocks.length + 1 := by
                  calc
                    blockId =
                        (blockId - before.blocks.length) +
                          before.blocks.length :=
                      (Nat.sub_add_cancel sourceLe).symm
                    _ = before.blocks.length + 1 := by
                      simp [offset, Nat.add_comm]
                subst blockId
                have copied :=
                  RootLabels.split_right_root?
                    (n := n) labels source prefixLength
                rw [sourceRootFound] at copied
                rw [← aligned] at labelFound
                rw [copied] at labelFound
                exact Option.some.inj labelFound
            have sourceLabelFound :
                RootLabels.root? labels source = some root := by
              rw [sourceLabel] at sourceRootFound
              exact sourceRootFound
            have offsetLt :
                blockId - before.blocks.length < 2 :=
              (List.getElem?_eq_some_iff.mp blockFound).1
            rcases
                Nat.le_one_iff_eq_zero_or_eq_one.mp
                  (Nat.le_of_lt_succ offsetLt) with
              offset | offset
            · simp [offset] at blockFound
              subst block
              have oldMixed :
                  BlockClockMixedAt clock cutoff sourceBlock := by
                apply BlockClockMixedAt.of_sublist
                  (small :=
                    { sourceBlock with
                      elements := sourceBlock.elements.take prefixLength })
                  (large := sourceBlock)
                · exact
                    List.take_sublist prefixLength sourceBlock.elements
                · exact ordered source sourceBlock sourceFound
                · simpa [EpisodeClock.after] using mixed
              exact
                Or.inl ⟨source, sourceBlock, sourceFound,
                  sourceLabelFound, oldMixed, by simp,
                  Or.inr ⟨source, prefixLength, rfl, rfl,
                    by
                      have sourceLe :
                          before.blocks.length ≤ blockId :=
                        Nat.le_of_not_gt (by simpa using old)
                      left
                      calc
                        blockId =
                            (blockId - before.blocks.length) +
                              before.blocks.length :=
                          (Nat.sub_add_cancel sourceLe).symm
                        _ = before.blocks.length := by simp [offset]⟩⟩
            · simp [offset] at blockFound
              subst block
              have oldMixed :
                  BlockClockMixedAt clock cutoff sourceBlock := by
                apply BlockClockMixedAt.of_sublist
                  (small :=
                    { sourceBlock with
                      elements := sourceBlock.elements.drop prefixLength })
                  (large := sourceBlock)
                · exact
                    List.drop_sublist prefixLength sourceBlock.elements
                · exact ordered source sourceBlock sourceFound
                · simpa [EpisodeClock.after] using mixed
              exact
                Or.inl ⟨source, sourceBlock, sourceFound,
                  sourceLabelFound, oldMixed, by simp,
                  Or.inr ⟨source, prefixLength, rfl, rfl,
                    by
                      have sourceLe :
                          before.blocks.length ≤ blockId :=
                        Nat.le_of_not_gt (by simpa using old)
                      right
                      calc
                        blockId =
                            (blockId - before.blocks.length) +
                              before.blocks.length :=
                          (Nat.sub_add_cancel sourceLe).symm
                        _ = before.blocks.length + 1 := by
                          simp [offset, Nat.add_comm]⟩⟩
  | valueChange changed delta =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      cases step.2.1 with
      | decrease canDecrease blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          exact
            Or.inl ⟨blockId, block, blockFound, labelBefore,
              by simpa [EpisodeClock.after] using mixed,
              by simp, Or.inl rfl⟩
      | increase canIncrease blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          exact
            Or.inl ⟨blockId, block, blockFound, labelBefore,
              by simpa [EpisodeClock.after] using mixed,
              by simp, Or.inl rfl⟩

private theorem no_mixed_split_source
    {n : ℕ} {params : Parameters}
    {before after : State n} {source prefixLength : ℕ}
    {clock : EpisodeClock n} {cutoff : ℕ}
    (step :
      Step params before (.split source prefixLength) after)
    {block : Block n}
    (found : after.block? source = some block)
    (mixed : BlockClockMixedAt clock cutoff block) :
    False := by
  cases step.2.1 with
  | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
      rename_i sourceBlock
      have sourceLt : source < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp sourceFound).1
      unfold State.block? at found
      rw [blocksEq] at found
      unfold splitBlocks at found
      rw [List.getElem?_append] at found
      simp only [List.length_modify, sourceLt, if_pos] at found
      rw [List.getElem?_modify] at found
      unfold State.block? at sourceFound
      simp [sourceFound] at found
      subst block
      exact mixed.elements_ne_nil rfl

private theorem split_fresh_mixed_ids_eq
    {n : ℕ} {params : Parameters}
    {before after : State n} {source prefixLength : ℕ}
    {clock : EpisodeClock n} {cutoff : ℕ}
    (ordered : StateClockCutOrderedAt before clock cutoff)
    (step :
      Step params before (.split source prefixLength) after)
    {firstId secondId : BlockId} {firstBlock secondBlock : Block n}
    (firstFound : after.block? firstId = some firstBlock)
    (firstFresh :
      firstId = before.blocks.length ∨
        firstId = before.blocks.length + 1)
    (firstMixed : BlockClockMixedAt clock cutoff firstBlock)
    (secondFound : after.block? secondId = some secondBlock)
    (secondFresh :
      secondId = before.blocks.length ∨
        secondId = before.blocks.length + 1)
    (secondMixed : BlockClockMixedAt clock cutoff secondBlock) :
    firstId = secondId := by
  rcases firstFresh with firstLeft | firstRight
  · rcases secondFresh with secondLeft | secondRight
    · exact firstLeft.trans secondLeft.symm
    · cases step.2.1 with
      | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
          rename_i sourceBlock
          have sourceNodup : sourceBlock.elements.Nodup :=
            step.1.block_elements_nodup sourceFound
          subst firstId
          subst secondId
          unfold State.block? at firstFound secondFound
          rw [blocksEq] at firstFound secondFound
          simp [splitBlocks] at firstFound secondFound
          subst firstBlock
          subst secondBlock
          exact False.elim <|
            not_mixed_take_and_drop sourceNodup
              (ordered source sourceBlock sourceFound)
              ⟨firstMixed, secondMixed⟩
  · rcases secondFresh with secondLeft | secondRight
    · cases step.2.1 with
      | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
          rename_i sourceBlock
          have sourceNodup : sourceBlock.elements.Nodup :=
            step.1.block_elements_nodup sourceFound
          subst firstId
          subst secondId
          unfold State.block? at firstFound secondFound
          rw [blocksEq] at firstFound secondFound
          simp [splitBlocks] at firstFound secondFound
          subst firstBlock
          subst secondBlock
          exact False.elim <|
            not_mixed_take_and_drop sourceNodup
              (ordered source sourceBlock sourceFound)
              ⟨secondMixed, firstMixed⟩
    · exact firstRight.trans secondRight.symm

namespace RootClockCutUniqueAt

/--
The unique mixed block of every root lineage is preserved by one exact legal
step.  The exact ledger and sound episode clock are included in the interface
so this theorem composes directly with the other fixed-cut state invariants.
-/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {ledger : EpisodeLedger n} {clock : EpisodeClock n}
    {events : List (ValueChangeEvent n)}
    {operation : Operation n} {cutoff : ℕ}
    (exact : EpisodeLedger.ExactAt before labels ledger)
    (clockSound : EpisodeClock.SoundAt before ledger clock events)
    (aligned : labels.length = before.blocks.length)
    (phase : RootLineagePhase before labels)
    (ordered : StateClockCutOrderedAt before clock cutoff)
    (unique : RootClockCutUniqueAt before labels clock cutoff)
    (step : Step params before operation after) :
    RootClockCutUniqueAt after
      (RootLabels.after labels operation)
      (EpisodeClock.after events.length clock operation) cutoff := by
  have _afterOrdered :
      StateClockCutOrderedAt after
        (EpisodeClock.after events.length clock operation) cutoff :=
    StateClockCutOrderedAt.after_step exact clockSound ordered step
  have afterPhase :
      RootLineagePhase after (RootLabels.after labels operation) :=
    phase.after_step aligned step
  intro root firstId firstBlock secondId secondBlock
    firstFound firstLabel firstMixed
    secondFound secondLabel secondMixed
  have firstClassification :=
    after_mixed_predecessor_or_growing
      (events := events) aligned ordered step
      firstFound firstLabel firstMixed
  have secondClassification :=
    after_mixed_predecessor_or_growing
      (events := events) aligned ordered step
      secondFound secondLabel secondMixed
  rcases firstClassification with firstPredecessor | firstGrowing
  · rcases secondClassification with secondPredecessor | secondGrowing
    · obtain
          ⟨beforeFirstId, beforeFirstBlock, beforeFirstFound,
            beforeFirstLabel, beforeFirstMixed, _firstCount,
            firstRelation⟩ :=
        firstPredecessor
      obtain
          ⟨beforeSecondId, beforeSecondBlock, beforeSecondFound,
            beforeSecondLabel, beforeSecondMixed, _secondCount,
            secondRelation⟩ :=
        secondPredecessor
      have beforeIdsEq : beforeFirstId = beforeSecondId :=
        unique root
          beforeFirstId beforeFirstBlock
          beforeSecondId beforeSecondBlock
          beforeFirstFound beforeFirstLabel beforeFirstMixed
          beforeSecondFound beforeSecondLabel beforeSecondMixed
      rcases firstRelation with firstSame |
        ⟨firstSource, firstPrefix, firstOperation,
          firstPredSource, firstFresh⟩
      · rcases secondRelation with secondSame |
          ⟨secondSource, secondPrefix, secondOperation,
            secondPredSource, secondFresh⟩
        · exact
            firstSame.symm.trans <|
              beforeIdsEq.trans secondSame
        · subst operation
          have sourceEq :
              secondSource = firstId := by
            exact
              secondPredSource.symm.trans <|
                beforeIdsEq.symm.trans firstSame
          exact False.elim <|
            no_mixed_split_source step
              (by simpa [sourceEq] using firstFound)
              (by simpa [EpisodeClock.after] using firstMixed)
      · rcases secondRelation with secondSame |
          ⟨secondSource, secondPrefix, secondOperation,
            secondPredSource, secondFresh⟩
        · subst operation
          have sourceEq :
              firstSource = secondId := by
            exact
              firstPredSource.symm.trans <|
                beforeIdsEq.trans secondSame
          exact False.elim <|
            no_mixed_split_source step
              (by simpa [sourceEq] using secondFound)
              (by simpa [EpisodeClock.after] using secondMixed)
        · subst operation
          exact
            split_fresh_mixed_ids_eq ordered step
              firstFound firstFresh
              (by simpa [EpisodeClock.after] using firstMixed)
              secondFound secondFresh
              (by simpa [EpisodeClock.after] using secondMixed)
    · have secondSelf :
          RootLabels.root? (RootLabels.after labels operation) secondId =
            some secondId :=
        afterPhase.growingIsRoot
          secondId secondBlock secondFound secondGrowing
      rw [secondLabel] at secondSelf
      have rootEq : root = secondId :=
        Option.some.inj secondSelf
      subst root
      exact
        afterPhase.mixed_block_eq_root_of_growing
          secondFound secondGrowing
          firstFound firstLabel firstMixed
  · have firstSelf :
        RootLabels.root? (RootLabels.after labels operation) firstId =
          some firstId :=
      afterPhase.growingIsRoot
        firstId firstBlock firstFound firstGrowing
    rw [firstLabel] at firstSelf
    have rootEq : root = firstId :=
      Option.some.inj firstSelf
    subst root
    exact
      (afterPhase.mixed_block_eq_root_of_growing
        firstFound firstGrowing
        secondFound secondLabel secondMixed).symm

end RootClockCutUniqueAt

end Splay.Interface
