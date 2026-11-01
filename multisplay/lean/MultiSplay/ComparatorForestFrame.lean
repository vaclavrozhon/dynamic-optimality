import MultiSplay.ComparatorForestMemory
import MultiSplay.ComparatorGuardFrame

/-! # Framing the literal unselected component slots

A switch may change preferences inside an ancestor component's opaque exit.
The ancestor's endpoint and root remain fixed, so its projected BST remains
identical. This is stronger than equality of domains and does not assert
equality of the full preference states below the component root.
-/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open EndpointEncoding ClassicalSwitch CommonForest

theorem projectedTree_frame {lower upper : Nat} {reference : BST lower upper}
    {before after : State} {slot : Slot}
    (oldValid : slot.Valid before reference) (newValid : slot.Valid after reference)
    (oldFamily newFamily : Family) (same : oldFamily slot.endpoint = newFamily slot.endpoint) :
    projectedTree before oldFamily slot = projectedTree after newFamily slot := by
  have endpoint : finish (restrict before slot.rootAddress) slot.primary.toRaw =
      finish (restrict after slot.rootAddress) slot.primary.toRaw :=
    List.append_cancel_left (oldValid.continuation.symm.trans newValid.continuation)
  simp only [projectedTree,oldValid.start,newValid.start,same]
  exact ComparatorPrimary.projectedTree_state_congr slot.primary _ _ endpoint _ _

/-- The two selected projected trees execute the local word. The literal
remainder is retained, including ancestor components whose opaque subtrees
contain the switched reference node. -/
theorem program_of_partition {lower upper : Nat} (reference : BST lower upper)
    (before after : State) (oldFamily newFamily : Family)
    (source incoming target parked : Slot) (remainder : List Slot)
    (oldSlots : (slots before reference).Perm (source::incoming::remainder))
    (newSlots : (slots after reference).Perm (target::parked::remainder))
    (unchanged : ∀ slot ∈ remainder, oldFamily slot.endpoint = newFamily slot.endpoint)
    {word : List (Event Nat)} {work : Nat}
    (localRun : Program [projectedTree before oldFamily source,projectedTree before oldFamily incoming]
      word [projectedTree after newFamily target,projectedTree after newFamily parked] work) :
    Program (projectedForest before reference oldFamily) word
      (projectedForest after reference newFamily) work := by
  have frame : remainder.map (projectedTree before oldFamily) =
      remainder.map (projectedTree after newFamily) := by
    apply List.map_congr_left
    intro slot member
    have oldMember : slot ∈ slots before reference := oldSlots.mem_iff.mpr (by simp [member])
    have newMember : slot ∈ slots after reference := newSlots.mem_iff.mpr (by simp [member])
    exact projectedTree_frame (slots_valid before reference slot oldMember)
      (slots_valid after reference slot newMember) oldFamily newFamily (unchanged slot member)
  have first := Trace.single (Step.reorder (access := RootAccess) (prepare := RotationPreparation)
    (oldSlots.map (projectedTree before oldFamily)))
  simp only [List.map_cons,frame] at first
  have middle := localRun.context [] (remainder.map (projectedTree before oldFamily))
  rw [frame] at middle
  have last := Trace.single (Step.reorder (access := RootAccess) (prepare := RotationPreparation)
    (newSlots.map (projectedTree after newFamily)).symm)
  simpa only [projectedForest,List.map_cons,List.nil_append,List.cons_append,List.append_nil,
    Nat.zero_add,Nat.add_zero] using first.append (middle.append last)

end MultiSplay.ComparatorForest
