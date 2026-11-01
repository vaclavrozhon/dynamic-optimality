import Splay.Accounting.ArticleBoundaryRelocationFootprint
import Splay.Accounting.BoundaryPairingMove
import Splay.Lazy.VisibleTraceCreator

namespace Splay.Accounting

open Splay.Lazy

private theorem normalizedInsertEvents_decompose {n : ℕ} (state : Lazy.State n)
    (id : Interface.BlockId) (block : Lazy.Block n) (element : Interface.Element n) :
    ∃ front suffix, state.normalizedInsertEvents id block element =
      front ++ .operation (.insert id element) :: suffix := by
  let target := Analysis.transientContractedGap (state.view.rawGap element) 0
  let prepared := state.adjustValue element target
  let creatorPrepared := prepared.adjustValue block.creator 1
  let insertPrepared := creatorPrepared.adjustValue element 2
  let inserted := insertPrepared.insert id element
  let elementRestored := inserted.adjustValue element (prepared.value element)
  refine ⟨state.adjustValueEvents element target ++ prepared.adjustValueEvents block.creator 1 ++
      creatorPrepared.adjustValueEvents element 2,
    inserted.adjustValueEvents element (prepared.value element) ++
      elementRestored.adjustValueEvents block.creator (prepared.value block.creator), ?_⟩
  simp only [State.normalizedInsertEvents, State.safeInsertEvents,
    target, prepared, creatorPrepared, insertPrepared, inserted, elementRestored,
    List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]

/-- The boundary implementation exposes both visible occurrences at their
actual chronological positions, including the immutable winner creator. -/
theorem boundaryRelocation_exists_move {n : ℕ} {params : Interface.Parameters}
    {initial : Lazy.State n} {sourceId destinationId : Interface.BlockId}
    {element : Interface.Element n} {afterView : HeapView n}
    (relocation : BoundaryRelocation params initial sourceId destinationId element afterView)
    (slot : PairingSlot) :
    Nonempty { move : BoundaryPairingMove relocation.trace //
      move.slot = slot ∧ move.winner = relocation.destination.owner ∧ move.loser = element ∧
        move.source = sourceId ∧ move.destination = destinationId ∧ move.deleteEventIndex = 0 } := by
  have deleteFound : relocation.events[0]? = some (.operation (.delete sourceId element)) := by
    rw [relocation.events_eq]
    simp
  obtain ⟨deleteOperationIndex, deleteBefore, deleteAfter, deleteAt⟩ :=
    relocation.trace.exists_visibleStepAt_event 0 (.delete sourceId element) deleteFound
  let detached := initial.delete sourceId element relocation.intervalGap
  let target := fun queried => Analysis.transientContractedGap (initial.view.rawGap queried) relocation.intervalGap
  let normalized := detached.adjustValues target (relocation.source.elements.erase element)
  obtain ⟨insertPrefix, suffix, insertionEq⟩ :=
    normalizedInsertEvents_decompose (normalized.replaceView afterView) destinationId relocation.destination element
  let front := [.operation (.delete sourceId element)] ++
    detached.adjustValuesEvents target (relocation.source.elements.erase element) ++ [.silent] ++ insertPrefix
  have eventsEq : relocation.events = front ++ .operation (.insert destinationId element) :: suffix := by
    rw [relocation.events_eq]
    change [.operation (.delete sourceId element)] ++
      detached.adjustValuesEvents target (relocation.source.elements.erase element) ++ [.silent] ++
      (normalized.replaceView afterView).normalizedInsertEvents destinationId relocation.destination element = _
    rw [insertionEq]
    simp [front, List.append_assoc]
  have prefixPositive : 0 < front.length := by simp [front]
  have insertFound : relocation.events[front.length]? = some (.operation (.insert destinationId element)) := by
    rw [eventsEq]
    simp
  obtain ⟨insertOperationIndex, insertBefore, insertAfter, insertAt⟩ :=
    relocation.trace.exists_visibleStepAt_event front.length (.insert destinationId element) insertFound
  have originalFound : initial.toInterface.block? destinationId = some relocation.destination.toInterface := by
    change (initial.blocks.map Lazy.Block.toInterface)[destinationId]? = _
    rw [List.getElem?_map, relocation.destinationFound]
    rfl
  obtain ⟨destinationBlock, destinationFound, destinationCreator⟩ := insertAt.creatorFound originalFound
  have ownerCreator := (relocation.trace.initial_valid.2 relocation.destination
    (List.mem_of_getElem? relocation.destinationFound)).owner_eq_creator_of_growing relocation.destinationGrowing
  refine ⟨⟨{
    slot, winner := relocation.destination.owner, loser := element,
    source := sourceId, deleteOperationIndex, deleteEventIndex := 0, deleteBefore, deleteAfter, deleteAt,
    destination := destinationId, insertOperationIndex, insertEventIndex := front.length,
    insertBefore, insertAfter, insertAt, delete_before_insert := prefixPositive,
    destinationBlock, destinationFound, destinationCreator := ?_
  }, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  exact destinationCreator.trans ownerCreator.symm

end Splay.Accounting
