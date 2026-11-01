import Splay.Interface.RootPhaseHistory

namespace Splay.Interface

/--
Every ghost root stored in the label array is the identifier of an existing
block.  This is stronger than mere alignment and records the fact that root
labels are introduced only by `create` and copied only by `split`.
-/
def RootLabels.RootsRealized {n : ℕ}
    (state : State n) (labels : RootLabels) : Prop :=
  ∀ blockId root,
    RootLabels.root? labels blockId = some root →
      ∃ rootBlock, state.block? root = some rootBlock

/--
While a lineage root is still growing, no distinct block of that lineage can
contain an element.  Descendants are created only by splitting a shrinking
block, and a shrinking root can never become growing again.
-/
def GrowingRootIsOnlyLineageBlockWithElements {n : ℕ}
    (state : State n) (labels : RootLabels) : Prop :=
  ∀ root rootBlock,
    state.block? root = some rootBlock →
      rootBlock.mode = .growing →
        ∀ blockId block,
          state.block? blockId = some block →
            RootLabels.root? labels blockId = some root →
              block.elements ≠ [] →
                blockId = root

/-- The two root-lineage phase facts used by temporal incidence. -/
structure RootLineagePhase {n : ℕ}
    (state : State n) (labels : RootLabels) : Prop where
  growingIsRoot : GrowingIsLineageRoot state labels
  rootsRealized : labels.RootsRealized state
  growingOnly : GrowingRootIsOnlyLineageBlockWithElements state labels

namespace RootLabels.RootsRealized

/-- Empty labels realize vacuously in an empty-block initial state. -/
theorem initial {n : ℕ} {params : Parameters} {state : State n}
    (initialState : state.Initial params) :
    RootLabels.RootsRealized state [] := by
  intro blockId root found
  simp [RootLabels.root?] at found

/-- A root occurring anywhere in a realized label array has a root block. -/
theorem exists_block_of_mem
    {n : ℕ} {state : State n} {labels : RootLabels}
    (realized : RootLabels.RootsRealized state labels)
    {root : RootId} (member : root ∈ labels) :
    ∃ rootBlock, state.block? root = some rootBlock := by
  obtain ⟨blockId, found⟩ := List.mem_iff_getElem?.mp member
  exact realized blockId root found

/-- An existing block identifier remains in range after every operation. -/
private theorem exists_after_of_exists_before
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (step : Step params before operation after)
    {blockId : BlockId} {block : Block n}
    (found : before.block? blockId = some block) :
    ∃ afterBlock, after.block? blockId = some afterBlock := by
  have beforeLt :
      blockId < before.blocks.length :=
    (List.getElem?_eq_some_iff.mp found).1
  have lengthEq := step.2.1.blocks_length
  have afterLt : blockId < after.blocks.length := by
    rw [lengthEq]
    exact beforeLt.trans_le
      (Nat.le_add_right before.blocks.length operation.blockIncrease)
  exact
    ⟨after.blocks[blockId],
      List.getElem?_eq_getElem afterLt⟩

/-- Root-label realization is preserved by one aligned legal operation. -/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n}
    (realized : RootLabels.RootsRealized before labels)
    (aligned : labels.length = before.blocks.length)
    (step : Step params before operation after) :
    RootLabels.RootsRealized after
      (RootLabels.after labels operation) := by
  intro blockId root found
  have rootMember :
      root ∈ RootLabels.after labels operation := by
    exact List.mem_iff_getElem?.mpr ⟨blockId, found⟩
  cases operation with
  | convert source =>
      have oldMember : root ∈ labels := by
        simpa [RootLabels.after] using rootMember
      obtain ⟨rootBlock, rootFound⟩ :=
        realized.exists_block_of_mem oldMember
      exact exists_after_of_exists_before step rootFound
  | create creator =>
      simp [RootLabels.after] at rootMember
      rcases rootMember with oldMember | freshMember
      · obtain ⟨rootBlock, rootFound⟩ :=
          realized.exists_block_of_mem oldMember
        exact exists_after_of_exists_before step rootFound
      · have rootEq : root = labels.length := by
          simpa using freshMember
        subst root
        have afterLt : labels.length < after.blocks.length := by
          have lengthEq := step.2.1.blocks_length
          simp [Operation.blockIncrease] at lengthEq
          rw [lengthEq, aligned]
          exact Nat.lt_succ_self _
        exact
          ⟨after.blocks[labels.length],
            List.getElem?_eq_getElem afterLt⟩
  | insert target element =>
      have oldMember : root ∈ labels := by
        simpa [RootLabels.after] using rootMember
      obtain ⟨rootBlock, rootFound⟩ :=
        realized.exists_block_of_mem oldMember
      exact exists_after_of_exists_before step rootFound
  | delete source element =>
      have oldMember : root ∈ labels := by
        simpa [RootLabels.after] using rootMember
      obtain ⟨rootBlock, rootFound⟩ :=
        realized.exists_block_of_mem oldMember
      exact exists_after_of_exists_before step rootFound
  | pass source matching =>
      have oldMember : root ∈ labels := by
        simpa [RootLabels.after] using rootMember
      obtain ⟨rootBlock, rootFound⟩ :=
        realized.exists_block_of_mem oldMember
      exact exists_after_of_exists_before step rootFound
  | split source prefixLength =>
      obtain ⟨sourceRoot, sourceRootFound⟩ :=
        (HistoryStep.mk step rfl).split_source_root_exists aligned
      have appendedMember :
          root ∈ labels ++ [sourceRoot, sourceRoot] := by
        simpa [RootLabels.after, sourceRootFound] using rootMember
      rcases List.mem_append.mp appendedMember with
        oldMember | copiedMember
      · obtain ⟨rootBlock, rootFound⟩ :=
          realized.exists_block_of_mem oldMember
        exact exists_after_of_exists_before step rootFound
      · have rootEq : root = sourceRoot := by
          simpa using copiedMember
        subst root
        obtain ⟨sourceRootBlock, rootFound⟩ :=
          realized source sourceRoot sourceRootFound
        exact exists_after_of_exists_before step rootFound
  | valueChange element delta =>
      have oldMember : root ∈ labels := by
        simpa [RootLabels.after] using rootMember
      obtain ⟨rootBlock, rootFound⟩ :=
        realized.exists_block_of_mem oldMember
      exact exists_after_of_exists_before step rootFound

end RootLabels.RootsRealized

namespace RootLineagePhase

/-- The genuine empty interface state satisfies the full root phase. -/
theorem initial {n : ℕ} {params : Parameters} {state : State n}
    (initialState : state.Initial params) :
    RootLineagePhase state [] := by
  refine
    { growingIsRoot := ?_
      rootsRealized := RootLabels.RootsRealized.initial initialState
      growingOnly := ?_ }
  · intro blockId block found
    simp [State.block?, initialState.2] at found
  · intro root rootBlock rootFound
    simp [State.block?, initialState.2] at rootFound

private theorem mode_lookup_modify
    {n : ℕ} (blocks : List (Block n)) (index query : ℕ)
    (update : Block n → Block n)
    (modeEq : ∀ block, (update block).mode = block.mode) :
    ((blocks.modify index update)[query]?).map Block.mode =
      (blocks[query]?).map Block.mode := by
  rw [List.getElem?_modify]
  cases found : blocks[query]? with
  | none =>
      simp [found]
  | some block =>
      by_cases same : index = query
      · simp [found, same, modeEq]
      · simp [found, same]

private theorem mode_lookup_insertAtDestinations
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n)) (query : ℕ) :
    ((insertAtDestinations blocks matching)[query]?).map Block.mode =
      (blocks[query]?).map Block.mode := by
  induction matching generalizing blocks with
  | nil =>
      rfl
  | cons pairing matching ih =>
      rw [show
        insertAtDestinations blocks (pairing :: matching) =
          insertAtDestinations
            (blocks.modify pairing.destination fun destination =>
              { destination with
                elements := pairing.loser :: destination.elements })
            matching by rfl]
      rw [ih]
      exact
        mode_lookup_modify blocks pairing.destination query
          (fun destination =>
            { destination with
              elements := pairing.loser :: destination.elements })
          (by intro destination; rfl)

@[simp]
private theorem removeLosers_nil {n : ℕ}
    (matching : List (Pairing n)) :
    removeLosers ([] : List (Element n)) matching = [] := by
  induction matching with
  | nil =>
      rfl
  | cons pairing matching ih =>
      simpa [removeLosers] using ih

private theorem mode_lookup_passBlocks
    {n : ℕ} (blocks : List (Block n))
    (sourceId query : ℕ) (source : Block n)
    (sourceFound : blocks[sourceId]? = some source)
    (matching : List (Pairing n)) :
    ((passBlocks blocks sourceId source matching)[query]?).map Block.mode =
      (blocks[query]?).map Block.mode := by
  unfold passBlocks
  rw [mode_lookup_insertAtDestinations]
  rw [List.getElem?_modify]
  cases originalFound : blocks[query]? with
  | none =>
      simp [originalFound]
  | some original =>
      by_cases same : sourceId = query
      · subst query
        rw [sourceFound] at originalFound
        have originalEq : original = source :=
          Option.some.inj originalFound.symm
        subst original
        simp [sourceFound]
      · simp [originalFound, same]

/--
No operation turns an already existing block from shrinking back to growing.
-/
private theorem growing_before_of_growing_after
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (step : Step params before operation after)
    {blockId : BlockId} {beforeBlock afterBlock : Block n}
    (beforeFound : before.block? blockId = some beforeBlock)
    (afterFound : after.block? blockId = some afterBlock)
    (afterGrowing : afterBlock.mode = .growing) :
    beforeBlock.mode = .growing := by
  unfold State.block? at beforeFound afterFound
  cases effectEq : step.2.1 with
  | convert found growing blocksEq valuesEq =>
      rename_i sourceId source
      rw [blocksEq] at afterFound
      rw [List.getElem?_modify] at afterFound
      by_cases same : sourceId = blockId
      · subst blockId
        change before.blocks[sourceId]? = some source at found
        rw [beforeFound] at found
        have sourceEq : source = beforeBlock :=
          Option.some.inj found.symm
        subst source
        simp [beforeFound] at afterFound
        subst afterBlock
        simp at afterGrowing
      · simp [beforeFound, same] at afterFound
        subst afterBlock
        exact afterGrowing
  | create room blocksEq valuesEq =>
      have blockLt : blockId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp beforeFound).1
      rw [blocksEq, List.getElem?_append_left blockLt] at afterFound
      rw [beforeFound] at afterFound
      have blockEq : afterBlock = beforeBlock :=
        Option.some.inj afterFound.symm
      simpa [blockEq] using afterGrowing
  | insert found growing unassigned valueOrder blocksEq valuesEq =>
      rename_i target targetBlock inserted
      rw [blocksEq] at afterFound
      have modeEq :=
        mode_lookup_modify before.blocks target blockId
          (fun current =>
            { current with
              elements := inserted :: current.elements })
          (by intro current; rfl)
      rw [afterFound, beforeFound] at modeEq
      simp only [Option.map_some] at modeEq
      have modes : afterBlock.mode = beforeBlock.mode :=
        Option.some.inj modeEq
      exact modes.symm.trans afterGrowing
  | delete found shrinking present blocksEq valuesEq =>
      rename_i source sourceBlock deleted
      rw [blocksEq] at afterFound
      have modeEq :=
        mode_lookup_modify before.blocks source blockId
          (fun current =>
            { current with
              elements := current.elements.erase deleted })
          (by intro current; rfl)
      rw [afterFound, beforeFound] at modeEq
      simp only [Option.map_some] at modeEq
      have modes : afterBlock.mode = beforeBlock.mode :=
        Option.some.inj modeEq
      exact modes.symm.trans afterGrowing
  | pass found validMatching blocksEq valuesEq =>
      rename_i sourceId source matching
      rw [blocksEq] at afterFound
      have modeEq :=
        mode_lookup_passBlocks before.blocks sourceId blockId source
          (by simpa [State.block?] using found) matching
      rw [afterFound, beforeFound] at modeEq
      simp only [Option.map_some] at modeEq
      have modes : afterBlock.mode = beforeBlock.mode :=
        Option.some.inj modeEq
      exact modes.symm.trans afterGrowing
  | split found shrinking prefixLe blocksEq valuesEq =>
      rename_i sourceId source prefixLength
      have blockLt : blockId < before.blocks.length :=
        (List.getElem?_eq_some_iff.mp beforeFound).1
      rw [blocksEq] at afterFound
      unfold splitBlocks at afterFound
      rw [List.getElem?_append_left (by simpa using blockLt)] at afterFound
      have modeEq :=
        mode_lookup_modify before.blocks sourceId blockId
          (fun current => { current with elements := [] })
          (by intro current; rfl)
      rw [afterFound, beforeFound] at modeEq
      simp only [Option.map_some] at modeEq
      have modes : afterBlock.mode = beforeBlock.mode :=
        Option.some.inj modeEq
      exact modes.symm.trans afterGrowing
  | decrease canDecrease blocksEq valuesEq =>
      rw [blocksEq, beforeFound] at afterFound
      have blockEq : afterBlock = beforeBlock :=
        Option.some.inj afterFound.symm
      simpa [blockEq] using afterGrowing
  | increase canIncrease blocksEq valuesEq =>
      rw [blocksEq, beforeFound] at afterFound
      have blockEq : afterBlock = beforeBlock :=
        Option.some.inj afterFound.symm
      simpa [blockEq] using afterGrowing

/-- A stable block identifier that is shrinking remains present and shrinking. -/
theorem shrinking_block_after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    (step : Step params before operation after)
    {blockId : BlockId} {block : Block n}
    (found : before.block? blockId = some block)
    (shrinking : block.mode = .shrinking) :
    ∃ afterBlock,
      after.block? blockId = some afterBlock ∧
        afterBlock.mode = .shrinking := by
  obtain ⟨afterBlock, afterFound⟩ :=
    RootLabels.RootsRealized.exists_after_of_exists_before step found
  refine ⟨afterBlock, afterFound, ?_⟩
  cases modeEq : afterBlock.mode with
  | growing =>
      have beforeGrowing :=
        growing_before_of_growing_after step found afterFound modeEq
      rw [shrinking] at beforeGrowing
      contradiction
  | shrinking =>
      rfl

namespace GrowingRootIsOnlyLineageBlockWithElements

/--
The unique nonempty-block phase is preserved by one aligned legal operation.
-/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n}
    (invariant :
      GrowingRootIsOnlyLineageBlockWithElements before labels)
    (growingIsRoot : GrowingIsLineageRoot before labels)
    (realized : RootLabels.RootsRealized before labels)
    (aligned : labels.length = before.blocks.length)
    (step : Step params before operation after) :
    GrowingRootIsOnlyLineageBlockWithElements after
      (RootLabels.after labels operation) := by
  intro root rootBlock rootFound rootGrowing
    blockId block blockFound labelFound nonempty
  cases operation with
  | convert sourceId =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      obtain ⟨beforeRoot, beforeRootFound⟩ :=
        realized blockId root labelBefore
      have beforeRootGrowing :=
        growing_before_of_growing_after step beforeRootFound
          rootFound rootGrowing
      cases step.2.1 with
      | convert sourceFound sourceGrowing blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          rw [List.getElem?_modify] at blockFound
          cases oldFound : before.blocks[blockId]? with
          | none =>
              simp [oldFound] at blockFound
          | some oldBlock =>
              by_cases same : sourceId = blockId
              · simp [oldFound, same] at blockFound
                subst block
                exact
                  invariant root beforeRoot beforeRootFound
                    beforeRootGrowing blockId oldBlock
                    (by simpa [State.block?] using oldFound)
                    labelBefore nonempty
              · simp [oldFound, same] at blockFound
                subst block
                exact
                  invariant root beforeRoot beforeRootFound
                    beforeRootGrowing blockId oldBlock
                    (by simpa [State.block?] using oldFound)
                    labelBefore nonempty
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
            obtain ⟨beforeRoot, beforeRootFound⟩ :=
              realized blockId root labelBefore
            have beforeRootGrowing :=
              growing_before_of_growing_after step beforeRootFound
                rootFound rootGrowing
            exact
              invariant root beforeRoot beforeRootFound
                beforeRootGrowing blockId block
                (by simpa [State.block?] using blockFound)
                labelBefore nonempty
          · simp only [old, if_false] at blockFound
            have offsetLt :
                blockId - before.blocks.length < 1 :=
              (List.getElem?_eq_some_iff.mp blockFound).1
            have offsetZero :
                blockId - before.blocks.length = 0 :=
              Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offsetLt)
            simp [offsetZero] at blockFound
            subst block
            simp at nonempty
  | insert target inserted =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      obtain ⟨beforeRoot, beforeRootFound⟩ :=
        realized blockId root labelBefore
      have beforeRootGrowing :=
        growing_before_of_growing_after step beforeRootFound
          rootFound rootGrowing
      cases step.2.1 with
      | insert targetFound targetGrowing unassigned valueOrder
          blocksEq valuesEq =>
          rename_i targetBlock
          by_cases same : target = blockId
          · subst blockId
            have targetSelf :=
              growingIsRoot target targetBlock targetFound targetGrowing
            rw [targetSelf] at labelBefore
            exact Option.some.inj labelBefore
          · unfold State.block? at blockFound
            rw [blocksEq] at blockFound
            rw [List.getElem?_modify] at blockFound
            cases oldFound : before.blocks[blockId]? with
            | none =>
                simp [oldFound] at blockFound
            | some oldBlock =>
                simp [oldFound, same] at blockFound
                subst block
                exact
                  invariant root beforeRoot beforeRootFound
                    beforeRootGrowing blockId oldBlock
                    (by simpa [State.block?] using oldFound)
                    labelBefore nonempty
  | delete source deleted =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      obtain ⟨beforeRoot, beforeRootFound⟩ :=
        realized blockId root labelBefore
      have beforeRootGrowing :=
        growing_before_of_growing_after step beforeRootFound
          rootFound rootGrowing
      cases step.2.1 with
      | delete sourceFound sourceShrinking present blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          rw [List.getElem?_modify] at blockFound
          cases oldFound : before.blocks[blockId]? with
          | none =>
              simp [oldFound] at blockFound
          | some oldBlock =>
              by_cases same : source = blockId
              · simp [oldFound, same] at blockFound
                subst block
                apply
                  invariant root beforeRoot beforeRootFound
                    beforeRootGrowing blockId oldBlock
                    (by simpa [State.block?] using oldFound)
                    labelBefore
                intro empty
                simp [empty] at nonempty
              · simp [oldFound, same] at blockFound
                subst block
                exact
                  invariant root beforeRoot beforeRootFound
                    beforeRootGrowing blockId oldBlock
                    (by simpa [State.block?] using oldFound)
                    labelBefore nonempty
  | pass source matching =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      obtain ⟨beforeRoot, beforeRootFound⟩ :=
        realized blockId root labelBefore
      have beforeRootGrowing :=
        growing_before_of_growing_after step beforeRootFound
          rootFound rootGrowing
      by_cases blockEq : blockId = root
      · exact blockEq
      · cases step.2.1 with
        | pass sourceFound validMatching blocksEq valuesEq =>
            rename_i sourceBlock
            have destinationsNe :
                ∀ pairing ∈ matching,
                  pairing.destination ≠ blockId := by
              intro pairing pairingMem destinationEq
              subst blockId
              obtain ⟨destination, destinationFound,
                  destinationGrowing, _creatorEq⟩ :=
                (validMatching.2.2.2.1 pairing pairingMem).2.2.2
              have destinationSelf :=
                growingIsRoot pairing.destination destination
                  destinationFound destinationGrowing
              rw [destinationSelf] at labelBefore
              exact blockEq (Option.some.inj labelBefore)
            unfold State.block? at blockFound
            rw [blocksEq] at blockFound
            unfold passBlocks at blockFound
            rw [block?_insertAtDestinations_of_ne
              _ matching blockId destinationsNe] at blockFound
            rw [List.getElem?_modify] at blockFound
            cases oldFound : before.blocks[blockId]? with
            | none =>
                simp [oldFound] at blockFound
            | some oldBlock =>
                by_cases same : source = blockId
                · subst blockId
                  change before.blocks[source]? = some sourceBlock at sourceFound
                  rw [oldFound] at sourceFound
                  have sourceEq : sourceBlock = oldBlock :=
                    Option.some.inj sourceFound.symm
                  subst sourceBlock
                  simp [oldFound] at blockFound
                  subst block
                  apply
                    invariant root beforeRoot beforeRootFound
                      beforeRootGrowing source oldBlock
                      (by simpa [State.block?] using oldFound)
                      labelBefore
                  intro empty
                  exact nonempty (by simp [empty])
                · simp [oldFound, same] at blockFound
                  subst block
                  exact
                    invariant root beforeRoot beforeRootFound
                      beforeRootGrowing blockId oldBlock
                      (by simpa [State.block?] using oldFound)
                      labelBefore nonempty
  | split source prefixLength =>
      have afterRootPhase :=
        growingIsRoot.after_step aligned step
      have rootSelf :=
        afterRootPhase root rootBlock rootFound rootGrowing
      have rootLtAfter :
          root < (RootLabels.after labels
            (.split source prefixLength)).length :=
        (List.getElem?_eq_some_iff.mp rootSelf).1
      cases step.2.1 with
      | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
          rename_i sourceBlock
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          unfold splitBlocks at blockFound
          rw [List.getElem?_append] at blockFound
          by_cases old : blockId < before.blocks.length
          · simp only [List.length_modify, old, if_pos] at blockFound
            have oldLabelLt : blockId < labels.length := by
              simpa [aligned] using old
            have labelBefore :
                RootLabels.root? labels blockId = some root := by
              simpa [RootLabels.after, RootLabels.root?,
                List.getElem?_append_left oldLabelLt] using labelFound
            obtain ⟨beforeRoot, beforeRootFound⟩ :=
              realized blockId root labelBefore
            have beforeRootGrowing :=
              growing_before_of_growing_after step beforeRootFound
                rootFound rootGrowing
            rw [List.getElem?_modify] at blockFound
            cases oldFound : before.blocks[blockId]? with
            | none =>
                simp [oldFound] at blockFound
            | some oldBlock =>
                by_cases same : source = blockId
                · simp [oldFound, same] at blockFound
                  subst block
                  simp at nonempty
                · simp [oldFound, same] at blockFound
                  subst block
                  exact
                    invariant root beforeRoot beforeRootFound
                      beforeRootGrowing blockId oldBlock
                      (by simpa [State.block?] using oldFound)
                      labelBefore nonempty
          · simp only [List.length_modify, old, if_false] at blockFound
            obtain ⟨sourceRoot, sourceRootFound⟩ :=
              (HistoryStep.mk step rfl).split_source_root_exists aligned
            have labelCopied : root = sourceRoot := by
              have offsetLt :
                  blockId - before.blocks.length < 2 :=
                (List.getElem?_eq_some_iff.mp blockFound).1
              have offsetCases :
                  blockId - before.blocks.length = 0 ∨
                    blockId - before.blocks.length = 1 :=
                Nat.le_one_iff_eq_zero_or_eq_one.mp
                  (Nat.le_of_lt_succ offsetLt)
              have sourceLe : before.blocks.length ≤ blockId :=
                Nat.le_of_not_gt old
              rcases offsetCases with offset | offset
              · have blockIdEq : blockId = before.blocks.length := by
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
                exact (Option.some.inj labelFound).symm
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
                exact (Option.some.inj labelFound).symm
            subst sourceRoot
            obtain ⟨beforeRoot, beforeRootFound⟩ :=
              realized source root sourceRootFound
            have beforeRootGrowing :=
              growing_before_of_growing_after step beforeRootFound
                rootFound rootGrowing
            have sourceNonempty : sourceBlock.elements ≠ [] := by
              intro empty
              have offsetLt :
                  blockId - before.blocks.length < 2 :=
                (List.getElem?_eq_some_iff.mp blockFound).1
              have offsetCases :
                  blockId - before.blocks.length = 0 ∨
                    blockId - before.blocks.length = 1 :=
                Nat.le_one_iff_eq_zero_or_eq_one.mp
                  (Nat.le_of_lt_succ offsetLt)
              rcases offsetCases with offset | offset <;>
                simp [empty, offset] at blockFound <;>
                subst block <;>
                exact nonempty rfl
            have sourceEqRoot :=
              invariant root beforeRoot beforeRootFound beforeRootGrowing
                source sourceBlock sourceFound sourceRootFound sourceNonempty
            subst source
            rw [beforeRootFound] at sourceFound
            have sourceBlockEq : sourceBlock = beforeRoot :=
              Option.some.inj sourceFound.symm
            subst sourceBlock
            simp [sourceShrinking] at beforeRootGrowing
  | valueChange changed delta =>
      have labelBefore :
          RootLabels.root? labels blockId = some root := by
        simpa [RootLabels.after] using labelFound
      obtain ⟨beforeRoot, beforeRootFound⟩ :=
        realized blockId root labelBefore
      have beforeRootGrowing :=
        growing_before_of_growing_after step beforeRootFound
          rootFound rootGrowing
      cases step.2.1 with
      | decrease canDecrease blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          exact
            invariant root beforeRoot beforeRootFound beforeRootGrowing
              blockId block blockFound labelBefore nonempty
      | increase canIncrease blocksEq valuesEq =>
          unfold State.block? at blockFound
          rw [blocksEq] at blockFound
          exact
            invariant root beforeRoot beforeRootFound beforeRootGrowing
              blockId block blockFound labelBefore nonempty

end GrowingRootIsOnlyLineageBlockWithElements

/-- The complete root-lineage phase is preserved by one aligned step. -/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n}
    (phase : RootLineagePhase before labels)
    (aligned : labels.length = before.blocks.length)
    (step : Step params before operation after) :
    RootLineagePhase after (RootLabels.after labels operation) := by
  refine
    { growingIsRoot :=
        phase.growingIsRoot.after_step aligned step
      rootsRealized :=
        phase.rootsRealized.after_step aligned step
      growingOnly := ?_ }
  exact
    GrowingRootIsOnlyLineageBlockWithElements.after_step
      phase.growingOnly phase.growingIsRoot
        phase.rootsRealized aligned step

end RootLineagePhase

namespace HistoryTrace

/-- The root-lineage phase is transported along an aligned history. -/
theorem rootLineagePhase
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    (phase : RootLineagePhase initial initialLabels) :
    RootLineagePhase final finalLabels := by
  induction history with
  | nil valid =>
      exact phase
  | @cons before middle after beforeLabels afterLabels
      operation operations head tail ih =>
      have middleAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      exact
        ih middleAligned (phase.after_step aligned head)

/-- Every endpoint reachable from an interface initial state has the phase. -/
theorem rootLineagePhase_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n} {finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial [] operations final finalLabels)
    (initialState : initial.Initial params) :
    RootLineagePhase final finalLabels := by
  apply history.rootLineagePhase
  · simp [initialState.2]
  · exact RootLineagePhase.initial initialState

end HistoryTrace

end Splay.Interface
