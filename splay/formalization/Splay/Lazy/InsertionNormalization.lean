import Splay.Lazy.TopmostInsertion

namespace Splay.Lazy.State

/-- Assigning the gap value to a detached non-root element preserves every
currently represented point gap. -/
theorem adjustValue_valuesRealizeGaps_of_unassigned {n : ℕ} {state : State n}
    (values : state.ValuesRealizeGaps) (element : Element n) (target : ℕ)
    (unassigned : element ∉ state.allElements) (notRoot : element ≠ state.view.root) :
    (state.adjustValue element target).ValuesRealizeGaps := by
  constructor
  · rw [adjustValue_view, adjustValue_value_of_ne state (Ne.symm notRoot)]
    exact values.1
  · intro block member queried inside
    rw [adjustValue_blocks] at member
    have different : queried ≠ element := by
      intro equal
      subst queried
      exact unassigned (State.mem_allElements_iff.mpr ⟨block, member, inside⟩)
    rw [adjustValue_value_of_ne state different, adjustValue_view]
    exact values.2 block member queried inside

/-- Insertion preserves the gap interpretation when the detached value has
already been set to the destination's growing point gap. -/
theorem insert_valuesRealizeGaps {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (growing : block.mode = .growing)
    (element : Element n)
    (target : state.value element = Analysis.transientContractedGap (state.view.rawGap element) 0) :
    (state.insert blockId element).ValuesRealizeGaps := by
  have zeroGap := (valid.2 block (List.mem_of_getElem? found)).growing_intervalGap_eq_zero growing
  refine ⟨values.1, ?_⟩
  intro current currentMember queried queriedMember
  obtain ⟨id, currentFound⟩ := List.mem_iff_getElem?.mp currentMember
  change (state.blocks.modify blockId fun b => b.inserted element)[id]? = some current at currentFound
  rw [List.getElem?_modify] at currentFound
  split at currentFound
  next selected =>
    have oldFound : state.blocks[id]? = some block := by simpa [selected] using found
    rw [oldFound] at currentFound
    have currentEq : block.inserted element = current := by simpa using currentFound
    rw [← currentEq] at queriedMember ⊢
    change queried ∈ element :: block.elements at queriedMember
    change state.value queried = Analysis.transientContractedGap (state.view.rawGap queried) block.intervalGap
    rcases List.mem_cons.mp queriedMember with rfl | oldMember
    · rw [zeroGap]
      exact target
    · exact values.2 block (List.mem_of_getElem? found) queried oldMember
  next other =>
    have oldFound : state.blocks[id]? = some current := by simpa using currentFound
    exact values.2 current (List.mem_of_getElem? oldFound) queried queriedMember

/-- Exact normalization and safe insertion events for one boundary loser. -/
def normalizedInsertEvents {n : ℕ} (state : State n)
    (blockId : Interface.BlockId) (block : Block n) (element : Element n) : List (Event n) :=
  let target := Analysis.transientContractedGap (state.view.rawGap element) 0
  let prepared := state.adjustValue element target
  state.adjustValueEvents element target ++ prepared.safeInsertEvents blockId block element

/-- A boundary insertion into a nonempty growing interval uses one insert and
at most four value bounds of unit increases, including all restorations. -/
theorem normalizedInsert_trace {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (growing : block.mode = .growing)
    (element : Element n) (unassigned : element ∉ state.allElements)
    (elementGap : 0 ≤ state.view.rawGap element)
    (bounded : Analysis.transientContractedGap (state.view.rawGap element) 0 ≤ params.valueBound)
    (first : ∃ suffix, state.view.topDown block.owner block.side = element :: block.elements ++ suffix) :
    let target := Analysis.transientContractedGap (state.view.rawGap element) 0
    let final := (state.adjustValue element target).insert blockId element
    Trace params state (state.normalizedInsertEvents blockId block element) final ∧
      final.ValuesRealizeGaps ∧
      Interface.totalInserts (eraseOperations (state.normalizedInsertEvents blockId block element)) = 1 ∧
      Interface.totalIncreases (eraseOperations (state.normalizedInsertEvents blockId block element)) ≤
        4 * params.valueBound := by
  dsimp only
  let target := Analysis.transientContractedGap (state.view.rawGap element) 0
  let prepared := state.adjustValue element target
  have positive : 1 ≤ target := by simp [target, Analysis.transientContractedGap, Analysis.contractedGap]
  have adjustment := state.adjustValue_trace element target valid positive bounded
  have preparedValid : prepared.Valid params := adjustment.final_valid
  have preparedFound : prepared.blocks[blockId]? = some block := by simpa [prepared] using found
  have preparedUnassigned : element ∉ prepared.allElements := by
    simpa [prepared, State.allElements] using unassigned
  have preparedFirst : ∃ suffix, prepared.view.topDown block.owner block.side =
      element :: block.elements ++ suffix := by simpa [prepared] using first
  have insertion := safeInsert_trace_of_first preparedValid preparedFound growing element
    preparedUnassigned (by simpa [prepared] using elementGap) preparedFirst
  have notRoot : element ≠ state.view.root := by
    obtain ⟨suffix, order⟩ := first
    have parent := (state.view.mem_topDown_iff.mp (by rw [order]; simp :
      element ∈ state.view.topDown block.owner block.side)).1
    intro equal
    rw [equal, state.view.root_parent] at parent
    contradiction
  have preparedValues := adjustValue_valuesRealizeGaps_of_unassigned values element target unassigned notRoot
  have insertedValues := insert_valuesRealizeGaps preparedValid preparedValues preparedFound growing element
    (by simpa only [prepared, adjustValue_view] using state.adjustValue_value_self element target positive)
  have increases := prepared.safeInsertEvents_totalIncreases_le blockId block element preparedValid
  have adjustmentCost := (state.totalIncreases_adjustValueEvents_le element target).trans bounded
  refine ⟨adjustment.append insertion, insertedValues, ?_, ?_⟩
  · simp only [normalizedInsertEvents, eraseOperations_append, Interface.totalInserts_append,
      totalInserts_adjustValueEvents, safeInsertEvents_totalInserts, Nat.zero_add]
  · change Interface.totalIncreases (eraseOperations
      (state.adjustValueEvents element target ++ prepared.safeInsertEvents blockId block element)) ≤ _
    rw [eraseOperations_append, Interface.totalIncreases_append]
    omega

end Splay.Lazy.State
