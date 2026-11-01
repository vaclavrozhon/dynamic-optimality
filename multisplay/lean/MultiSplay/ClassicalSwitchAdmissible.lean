import MultiSplay.ClassicalSwitchWord

/-! # Every prescribed classical split cuts at a unique present pivot -/

namespace MultiSplay.ClassicalSwitch

open CommonForest

variable {α : Type*}

theorem leftWord_canSplay (lower upper : Boundary α) (old incoming : List α) (pivot : α)
    (unique : (lower.lowerKeys ++ old ++ [pivot] ++ upper.upperKeys).Nodup) :
    ∀ event ∈ leftWord lower upper old incoming pivot, event.CanSplay := by
  cases lower <;> cases upper <;>
    simp_all [leftWord, leftToRightWord, noLowerWord, noUpperWord, noGuardsWord,
      Event.CanSplay, Boundary.lowerKeys, Boundary.upperKeys, List.nodup_append',
      List.disjoint_append_right, and_assoc, ne_comm]

theorem canSplay_mirror (event : Event α) : event.mirror.CanSplay ↔ event.CanSplay := by
  cases event <;> simp [Event.mirror, Event.CanSplay, and_comm]

theorem word_canSplay (oldSide : Bool) (lower upper : Boundary α) (old incoming : List α) (pivot : α)
    (unique : (beforeKeys oldSide lower upper old pivot).Nodup) :
    ∀ event ∈ word oldSide lower upper old incoming pivot, event.CanSplay := by
  cases oldSide with
  | false =>
      simpa [word] using leftWord_canSplay lower upper old incoming pivot
        (by simpa [beforeKeys, List.append_assoc] using unique)
  | true =>
      have reflected : (upper.reflect.lowerKeys ++ old.reverse ++ [pivot] ++ lower.reflect.upperKeys).Nodup := by
        have reversed : (beforeKeys true lower upper old pivot).reverse.Nodup := by
          simpa only [List.nodup_reverse] using unique
        simpa [beforeKeys, List.reverse_append, List.append_assoc] using reversed
      intro event member
      obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
      exact (canSplay_mirror source).mpr
        (leftWord_canSplay upper.reflect lower.reflect old.reverse incoming.reverse pivot reflected source present)

end MultiSplay.ClassicalSwitch
