import Splay.Lazy.VisibleTraceOccurrence
import Splay.Interface.PersistentCreators

namespace Splay.Lazy

/-- Silent view changes as well as visible operations retain old ID creators. -/
theorem Step.creatorFound {n : ℕ} {params : Interface.Parameters}
    {before after : State n} {event : Event n} (step : Step params before event after)
    {id : Interface.BlockId} {block : Interface.Block n}
    (found : before.toInterface.block? id = some block) :
    ∃ current : Interface.Block n, after.toInterface.block? id = some current ∧ current.creator = block.creator := by
  cases event with
  | operation operation => exact step.interfaceStep_of_operation.2.1.creatorFound found
  | silent =>
      exact ⟨block, by rw [← step.projection_eq_of_silent]; exact found, rfl⟩

/-- The pre-state of any actual visible occurrence retains every old creator. -/
theorem Trace.VisibleStepAt.creatorFound {n : ℕ} {params : Interface.Parameters}
    {initial final before after : State n} {events : List (Event n)}
    {trace : Trace params initial events final} {operationIndex eventIndex : ℕ}
    {operation : Interface.Operation n}
    (occurrence : Trace.VisibleStepAt trace operationIndex eventIndex before operation after)
    {id : Interface.BlockId} {block : Interface.Block n}
    (found : initial.toInterface.block? id = some block) :
    ∃ current : Interface.Block n, before.toInterface.block? id = some current ∧ current.creator = block.creator := by
  induction occurrence generalizing block with
  | head step tail => exact ⟨block, found, rfl⟩
  | visibleTail step tail occurrence ih =>
      obtain ⟨middle, middleFound, middleCreator⟩ := step.creatorFound found
      obtain ⟨current, currentFound, currentCreator⟩ := ih middleFound
      exact ⟨current, currentFound, currentCreator.trans middleCreator⟩
  | silentTail step tail occurrence ih =>
      obtain ⟨middle, middleFound, middleCreator⟩ := step.creatorFound found
      obtain ⟨current, currentFound, currentCreator⟩ := ih middleFound
      exact ⟨current, currentFound, currentCreator.trans middleCreator⟩

/-- A visible event at an exact rich-event index exposes its visible index
and its actual endpoints in this trace. -/
theorem Trace.exists_visibleStepAt_event {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (trace : Trace params initial events final) (index : ℕ) (operation : Interface.Operation n)
    (found : events[index]? = some (.operation operation)) :
    ∃ operationIndex before after,
      Trace.VisibleStepAt trace operationIndex index before operation after := by
  induction trace generalizing index with
  | nil valid => simp at found
  | @cons initial middle final event events head tail ih =>
      cases index with
      | zero =>
          have equal : event = .operation operation := by simpa using found
          subst event
          exact ⟨0, initial, middle, .head head tail⟩
      | succ index =>
          obtain ⟨operationIndex, before, after, occurrence⟩ := ih index (by simpa using found)
          cases event with
          | operation headOperation =>
              exact ⟨operationIndex.succ, before, after, .visibleTail head tail occurrence⟩
          | silent => exact ⟨operationIndex, before, after, .silentTail head tail occurrence⟩

end Splay.Lazy
