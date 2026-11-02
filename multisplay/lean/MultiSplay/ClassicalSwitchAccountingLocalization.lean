import MultiSplay.ClassicalSwitchLocalization
import MultiSplay.ClassicalSwitchFrame

/-! # A recursive physical switch emits exactly the original global word -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.Primary (Key)
open EndpointEncoding

variable {α : Type*}

theorem hole_owner_nonroot (state : State) (reference : RawTree α)
    {entry : Key × RawTree α} (member : entry ∈ preferredHoles state reference) (suffix : Key)
    (real : referenceAt reference (entry.1 ++ suffix) ≠ .empty) :
    startDepth state (entry.1 ++ suffix) ≠ 0 := by
  intro zero
  have path := path_at state reference (entry.1 ++ suffix) ((startDepth_zero _ _).mp zero) real
  exact path.hole_not_ancestor real member (List.prefix_append _ _)

/-- If the selected component starts below the root, removing that root from
the reference does not change any event, pivot, guard, or domain. -/
theorem eventWord_cons (state : State) (edge : Bool) (address : Key)
    (left right : RawTree α) (pivot : α)
    (nonroot : startDepth state (edge::address) ≠ 0)
    (real : referenceAt (.node left pivot right) (edge::address) ≠ .empty) :
    eventWord (.node left pivot right) state (edge::address) =
      eventWord (if edge then right else left) (below state edge) address := by
  have childReal : referenceAt (if edge then right else left) address ≠ .empty := real
  rw [eventWord_selected state (edge::address) real]
  simpa only [startDepth_cons_nonzero state edge address nonroot, List.take_succ_cons,
    List.drop_succ_cons, referenceAt, restrict] using
      (eventWord_selected (below state edge) address childReal).symm

/-- Recursing into an annotated opaque subtree preserves the exact global
event word. The only premises are its canonical occurrence and a real owner. -/
theorem eventWord_hole (state : State) (reference : RawTree α)
    {entry : Key × RawTree α} (member : entry ∈ preferredHoles state reference) (suffix : Key)
    (real : referenceAt reference (entry.1 ++ suffix) ≠ .empty) :
    eventWord reference state (entry.1 ++ suffix) =
      eventWord entry.2 (restrict state entry.1) suffix := by
  induction reference generalizing state entry with
  | empty => exact False.elim (real (referenceAt_empty _))
  | node left pivot right ihl ihr =>
      have nonroot := hole_owner_nonroot state (.node left pivot right) member suffix real
      cases side : state [] with
      | false =>
          simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte, List.mem_append,
            List.mem_singleton] at member
          rcases member with previous | rfl
          · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
            have first := eventWord_cons state false (child.1 ++ suffix) left right pivot nonroot real
            have rest := ihl (below state false) present real
            simpa only [List.cons_append, List.nil_append, restrict] using first.trans rest
          · simpa only [List.cons_append, List.nil_append, restrict, ↓reduceIte] using
              eventWord_cons state true suffix left right pivot nonroot real
      | true =>
          simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | previous
          · simpa only [List.cons_append, List.nil_append, restrict, Bool.false_eq_true, ↓reduceIte] using
              eventWord_cons state false suffix left right pivot nonroot real
          · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
            have first := eventWord_cons state true (child.1 ++ suffix) left right pivot nonroot real
            have rest := ihr (below state true) present real
            simpa only [List.cons_append, List.nil_append, restrict] using first.trans rest

end MultiSplay.ClassicalSwitch
