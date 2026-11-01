import Splay.Interface.PassCountHistory

namespace Splay.Interface

/-- Every live or administrative block has pass count at most `bound`. -/
def PassCountBound {n : ℕ} (state : State n) (bound : ℕ) : Prop :=
  ∀ blockId block,
    state.block? blockId = some block →
      block.passCount ≤ bound

private theorem lookup_modify_passCount
    {n : ℕ} (blocks : List (Block n)) (index : ℕ)
    (update : Block n → Block n) (bound : ℕ)
    (all :
      ∀ (blockId : ℕ) (block : Block n),
        blocks[blockId]? = some block →
          block.passCount ≤ bound)
    (preserves :
      ∀ block, block.passCount ≤ bound →
        (update block).passCount ≤ bound) :
    ∀ (blockId : ℕ) (block : Block n),
      (blocks.modify index update)[blockId]? = some block →
        block.passCount ≤ bound := by
  intro blockId block found
  rw [List.getElem?_modify] at found
  cases originalFound : blocks[blockId]? with
  | none =>
      simp [originalFound] at found
  | some original =>
      by_cases same : index = blockId
      · simp [originalFound, same] at found
        subst block
        exact preserves original (all blockId original originalFound)
      · simp [originalFound, same] at found
        subst block
        exact all blockId original originalFound

private theorem passCount_insertAtDestinations
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n)) (bound : ℕ)
    (all :
      ∀ (blockId : ℕ) (block : Block n),
        blocks[blockId]? = some block →
          block.passCount ≤ bound) :
    ∀ (blockId : ℕ) (block : Block n),
      (insertAtDestinations blocks matching)[blockId]? = some block →
        block.passCount ≤ bound := by
  induction matching generalizing blocks with
  | nil =>
      exact all
  | cons pairing matching ih =>
      apply ih
      apply lookup_modify_passCount blocks pairing.destination _ bound all
      intro destination destinationBound
      exact destinationBound

namespace PassCountBound

/-- One operation can increase the maximum pass count by at most one. -/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {operation : Operation n}
    {bound : ℕ}
    (bounded : PassCountBound before bound)
    (step : Step params before operation after) :
    PassCountBound after (bound + 1) := by
  intro query block afterFound
  unfold State.block? at afterFound
  cases step.2.1 with
  | convert sourceFound sourceGrowing blocksEq valuesEq =>
      rename_i sourceId source
      rw [blocksEq] at afterFound
      exact
        lookup_modify_passCount before.blocks sourceId
          (fun current => { current with mode := .shrinking })
          (bound + 1)
          (fun blockId original originalFound =>
            (bounded blockId original originalFound).trans
              (Nat.le_succ bound))
          (by
            intro original originalBound
            exact originalBound)
          query block afterFound
  | create room blocksEq valuesEq =>
      rw [blocksEq, List.getElem?_append] at afterFound
      by_cases old : query < before.blocks.length
      · simp only [old, if_pos] at afterFound
        exact
          (bounded query block afterFound).trans
            (Nat.le_succ bound)
      · simp only [old] at afterFound
        have offsetLt :
            query - before.blocks.length < 1 :=
          (List.getElem?_eq_some_iff.mp afterFound).choose
        have offsetZero : query - before.blocks.length = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offsetLt)
        simp [offsetZero] at afterFound
        subst block
        change 0 ≤ bound + 1
        omega
  | insert targetFound targetGrowing unassigned valueOrder
      blocksEq valuesEq =>
      rename_i targetId target element
      rw [blocksEq] at afterFound
      exact
        lookup_modify_passCount before.blocks targetId
          (fun current =>
            { current with elements := element :: current.elements })
          (bound + 1)
          (fun blockId original originalFound =>
            (bounded blockId original originalFound).trans
              (Nat.le_succ bound))
          (by
            intro original originalBound
            exact originalBound)
          query block afterFound
  | delete sourceFound sourceShrinking present blocksEq valuesEq =>
      rename_i sourceId source element
      rw [blocksEq] at afterFound
      exact
        lookup_modify_passCount before.blocks sourceId
          (fun current =>
            { current with elements := current.elements.erase element })
          (bound + 1)
          (fun blockId original originalFound =>
            (bounded blockId original originalFound).trans
              (Nat.le_succ bound))
          (by
            intro original originalBound
            exact originalBound)
          query block afterFound
  | pass sourceFound validMatching blocksEq valuesEq =>
      rename_i sourceId source matching
      rw [blocksEq] at afterFound
      unfold passBlocks at afterFound
      apply passCount_insertAtDestinations
          (before.blocks.modify sourceId fun _ =>
            { source with
              passCount := source.passCount + 1
              elements := removeLosers source.elements matching })
          matching (bound + 1)
      · intro blockId original originalFound
        rw [List.getElem?_modify] at originalFound
        cases beforeFound : before.blocks[blockId]? with
        | none =>
            simp [beforeFound] at originalFound
        | some beforeBlock =>
            by_cases same : sourceId = blockId
            · subst blockId
              unfold State.block? at sourceFound
              rw [sourceFound] at beforeFound
              have beforeEq : beforeBlock = source :=
                Option.some.inj beforeFound.symm
              subst beforeBlock
              simp [sourceFound] at originalFound
              subst original
              have sourceBound :=
                bounded sourceId source sourceFound
              change source.passCount + 1 ≤ bound + 1
              omega
            · simp [beforeFound, same] at originalFound
              subst original
              exact
                (bounded blockId beforeBlock beforeFound).trans
                  (Nat.le_succ bound)
      · exact afterFound
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
        exact
          lookup_modify_passCount before.blocks sourceId
            (fun current => { current with elements := [] })
            (bound + 1)
            (fun blockId original originalFound =>
              (bounded blockId original originalFound).trans
                (Nat.le_succ bound))
            (by
              intro original originalBound
              exact originalBound)
            query block afterFound
      · simp only [old] at afterFound
        simp only [List.length_modify] at afterFound
        have offsetLt :
            query - before.blocks.length < 2 :=
          (List.getElem?_eq_some_iff.mp afterFound).choose
        have offsetCases :
            query - before.blocks.length = 0 ∨
              query - before.blocks.length = 1 :=
          Nat.le_one_iff_eq_zero_or_eq_one.mp
            (Nat.le_of_lt_succ offsetLt)
        have sourceBound := bounded sourceId source sourceFound
        rcases offsetCases with offset | offset <;>
          simp [offset] at afterFound <;>
          subst block <;>
          change source.passCount ≤ bound + 1 <;>
          omega
  | decrease canDecrease blocksEq valuesEq =>
      exact
        (bounded query block
          (by simpa [State.block?, blocksEq] using afterFound)).trans
          (Nat.le_succ bound)
  | increase canIncrease blocksEq valuesEq =>
      exact
        (bounded query block
          (by simpa [State.block?, blocksEq] using afterFound)).trans
          (Nat.le_succ bound)

end PassCountBound

namespace HistoryTrace

/-- Starting from a `bound`-bounded state, a trace of length `m` ends with
pass counts bounded by `bound + m`. -/
theorem passCountBound_add_length
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    {bound : ℕ} (bounded : PassCountBound initial bound) :
    PassCountBound final (bound + operations.length) := by
  induction history generalizing bound with
  | nil valid =>
      simpa using bounded
  | @cons before middle after beforeLabels afterLabels operation operations
      head tail ih =>
      have next := bounded.after_step head
      have tailBound := ih next
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailBound

/-- Initial traces therefore have endpoint pass count at most their length. -/
theorem passCountBound_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial [] operations final finalLabels)
    (initialState : initial.Initial params) :
    PassCountBound final operations.length := by
  have initialBound : PassCountBound initial 0 := by
    intro blockId block found
    simp [State.block?, initialState.2] at found
  simpa using history.passCountBound_add_length initialBound

end HistoryTrace

namespace ActivityHistory

/--
Every activity occurrence's pre-pass count is strictly below the number of
operations remaining after adding the elapsed prefix.  At elapsed time zero,
this gives the finite tail range used by global decay.
-/
theorem occurrence_passCount_lt_add_length
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial initialLabels operations occurrences
        final finalLabels)
    {elapsed : ℕ}
    (bounded : PassCountBound initial elapsed)
    (aligned : initialLabels.length = initial.blocks.length) :
    ∀ occurrence ∈ occurrences,
      occurrence.passCount < elapsed + operations.length := by
  induction history generalizing elapsed with
  | nil valid =>
      simp
  | @cons before middle after beforeLabels afterLabels operation operations
      tailOccurrences head tail ih =>
      intro occurrence member
      rcases List.mem_append.mp member with headMember | tailMember
      · obtain ⟨source, matching, sourceBlock, pairing, sourceRoot,
          operationEq, sourceFound, rootFound, pairingMem,
          occurrenceEq⟩ :=
          mem_operationActivityOccurrences_of_step
            head aligned headMember
        subst occurrence
        have sourceBound := bounded source sourceBlock sourceFound
        simp only [List.length_cons]
        omega
      · have nextAligned :
            (RootLabels.after beforeLabels operation).length =
              middle.blocks.length :=
          (HistoryStep.mk head rfl).labels_length aligned
        have tailBound :=
          ih (bounded.after_step head) nextAligned
            occurrence tailMember
        simp only [List.length_cons]
        omega

/-- Zero-elapsed specialization for histories from an initial state. -/
theorem occurrence_passCount_lt_length_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {finalLabels : RootLabels}
    {operations : List (Operation n)}
    {occurrences : List (ActivityOccurrence n)}
    (history :
      ActivityHistory params initial [] operations occurrences
        final finalLabels)
    (initialState : initial.Initial params) :
    ∀ occurrence ∈ occurrences,
      occurrence.passCount < operations.length := by
  have initialBound : PassCountBound initial 0 := by
    intro blockId block found
    simp [State.block?, initialState.2] at found
  simpa using
    history.occurrence_passCount_lt_add_length initialBound
      (by simp [initialState.2])

end ActivityHistory

end Splay.Interface
