import Splay.Lazy.DeletionGeometry
import Splay.Interface.OperationCounts

namespace Splay.Lazy.State

/-- Recomputing a shrinking minimum after deletion never raises the target
value of a surviving source element. -/
theorem deleted_target_le {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (shrinking : block.mode = .shrinking)
    {element queried : Element n} {intervalGap : ℤ}
    (gapValid : (block.deleted element intervalGap).GapValid state.view)
    (survives : queried ∈ block.elements.erase element) :
    Analysis.transientContractedGap (state.view.rawGap queried) intervalGap ≤ state.value queried := by
  have blockMember := List.mem_of_getElem? found
  have oldMember := List.mem_of_mem_erase survives
  have oldMinimum := (valid.2 block blockMember).2.2
  simp only [Block.GapValid, shrinking] at oldMinimum
  rcases oldMinimum with ⟨empty, _⟩ | ⟨_, oldMinimum⟩
  · simp [empty] at oldMember
  have newMinimum := gapValid
  simp only [Block.GapValid, Block.deleted, shrinking] at newMinimum
  rcases newMinimum with ⟨empty, _⟩ | ⟨_, newMinimum⟩
  · simp [empty] at survives
  rw [values.2 block blockMember queried oldMember]
  apply Analysis.transientContractedGap_antitone_intervalGap
    (oldMinimum.le_of_subset newMinimum ?_)
    (newMinimum.interval_le (by simpa using survives))
  intro candidate member
  exact List.mem_toFinset.mpr (List.mem_of_mem_erase (List.mem_toFinset.mp member))

/-- A deletion followed only by downward value normalization. The final block
list is literally that of one deletion, so no new interval is created. -/
theorem exists_normalizedDeletion {n : ℕ} {params : Interface.Parameters} {state : State n}
    (valid : state.Valid params) (values : state.ValuesRealizeGaps)
    {blockId : Interface.BlockId} {block : Block n}
    (found : state.blocks[blockId]? = some block) (shrinking : block.mode = .shrinking)
    (element : Element n) (member : element ∈ block.elements) :
    ∃ intervalGap : ℤ,
      let detached := state.delete blockId element intervalGap
      let target := fun queried => Analysis.transientContractedGap (state.view.rawGap queried) intervalGap
      let survivors := block.elements.erase element
      let final := detached.adjustValues target survivors
      let events := [.operation (.delete blockId element)] ++ detached.adjustValuesEvents target survivors
      Trace params state events final ∧ final.ValuesRealizeGaps ∧
        Interface.totalInserts (eraseOperations events) = 0 ∧
        Interface.totalIncreases (eraseOperations events) = 0 ∧
        (∀ queried, final.value queried ≤ state.value queried) := by
  obtain ⟨intervalGap, gapValid⟩ := Block.exists_gapValid_of_shrinking state.view
    (block.deleted element 0) shrinking
  have deletion := delete_step_of_gapValid valid found shrinking element member intervalGap gapValid
  refine ⟨intervalGap, ?_⟩
  dsimp only
  let detached := state.delete blockId element intervalGap
  let target := fun queried => Analysis.transientContractedGap (state.view.rawGap queried) intervalGap
  let survivors := block.elements.erase element
  let final := detached.adjustValues target survivors
  let adjustmentEvents := detached.adjustValuesEvents target survivors
  have sourceMember := List.mem_of_getElem? found
  have sourceNodup : block.elements.Nodup :=
    (List.nodup_flatMap.mp valid.allElements_nodup).1 block sourceMember
  have survivorsNodup : survivors.Nodup := sourceNodup.erase element
  have positive : ∀ queried ∈ survivors, 1 ≤ target queried := by
    intros
    simp [target, Analysis.transientContractedGap, Analysis.contractedGap]
  have targetLe : ∀ queried ∈ survivors, target queried ≤ state.value queried := by
    intro queried survives
    exact deleted_target_le valid values found shrinking gapValid survives
  have targetBounded : ∀ queried ∈ survivors, target queried ≤ params.valueBound := by
    intro queried survives
    exact (targetLe queried survives).trans (valid.toInterface.2.1 queried).2
  have adjustments : Trace params detached adjustmentEvents final :=
    detached.adjustValues_trace target survivors deletion.after_valid positive targetBounded
  have finalView : final.view = state.view := by simp [final, detached, State.delete]
  have finalBlocks : final.blocks = detached.blocks := by simp [final]
  have finalValues : final.ValuesRealizeGaps := by
    unfold ValuesRealizeGaps
    rw [finalView]
    constructor
    ·
      have rootOutside : state.view.root ∉ survivors := by
        intro inside
        exact valid.root_not_mem (State.mem_allElements_iff.mpr
          ⟨block, sourceMember, List.mem_of_mem_erase inside⟩)
      rw [show final.value state.view.root = detached.value state.view.root from
        detached.adjustValues_value_of_not_mem target survivors rootOutside]
      exact values.1
    · intro current currentMember queried queriedMember
      rw [finalBlocks] at currentMember
      obtain ⟨id, currentFound⟩ := List.mem_iff_getElem?.mp currentMember
      change (state.blocks.modify blockId fun b => b.deleted element intervalGap)[id]? = some current at currentFound
      rw [List.getElem?_modify] at currentFound
      split at currentFound
      next selected =>
        have oldFound : state.blocks[id]? = some block := by simpa [selected] using found
        rw [oldFound] at currentFound
        have currentEq : block.deleted element intervalGap = current := by simpa using currentFound
        rw [← currentEq] at queriedMember ⊢
        exact detached.adjustValues_value_of_mem target survivorsNodup queriedMember positive
      next other =>
        have oldFound : state.blocks[id]? = some current := by simpa using currentFound
        have outside : queried ∉ survivors := by
          intro inside
          have idsEq := valid.blockId_eq_of_element_mem found (List.mem_of_mem_erase inside)
            oldFound queriedMember
          exact other idsEq
        rw [show final.value queried = detached.value queried from
          detached.adjustValues_value_of_not_mem target survivors outside]
        exact values.2 current (List.mem_of_getElem? oldFound) queried queriedMember
  refine ⟨Trace.cons deletion adjustments, finalValues, ?_, ?_, ?_⟩
  · simp only [eraseOperations_append, Interface.totalInserts_append,
      totalInserts_adjustValuesEvents_eq_zero]
    rfl
  · have noIncrease := detached.totalIncreases_adjustValuesEvents_eq_zero_of_le target
      survivors survivorsNodup targetLe
    simp only [eraseOperations_append, Interface.totalIncreases_append]
    have deleteZero : Interface.totalIncreases
        (eraseOperations [Event.operation (Interface.Operation.delete blockId element)]) = 0 := rfl
    rw [deleteZero, Nat.zero_add]
    exact noIncrease
  · intro queried
    by_cases inside : queried ∈ survivors
    · rw [show final.value queried = target queried from
        detached.adjustValues_value_of_mem target survivorsNodup inside positive]
      exact targetLe queried inside
    · rw [show final.value queried = detached.value queried from
        detached.adjustValues_value_of_not_mem target survivors inside]
      rfl

end Splay.Lazy.State
