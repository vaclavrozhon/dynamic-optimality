import TangoSquared.Paper20261030.VirtualPackedCursor
import TangoSquared.Paper20261030.SourceRecordMap

/-!
# Complete primary representations retaining the virtual cursor layout

A physical datum is either one source record or a complete bounded virtual
cursor. The latter contains at most two virtual keys, one ancestor frame,
and nine source records, as proved in `VirtualCursorSize`. Keeping it as a
bounded datum retains shape and cursor position in addition to records.

Real routing wings contain only source datums. Each component's bottom
original key stores one header datum. Recursive expansion therefore has
at most five such bounded datums (including attachment delimiters) at
each physical vertex and contains exactly the original ordered keys.
-/

namespace TangoSquared.Paper20261030.PackedPrimary

open PreferredProjection ColoredStorage PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

inductive Datum (ρ : Type*) where
  | record (value : ρ)
  | header (cursor : VirtualCursor Nat ρ)

def liftWing (wing : RoutingWing α ρ) : RoutingWing α (Datum ρ) :=
  wing.map (Source.mapRecords (List.map Datum.record))

theorem liftWing_word (wing : RoutingWing α ρ) : routingWord (liftWing wing) = routingWord wing := by
  cases wing with
  | none => rfl
  | some source => exact congrArg RouterProjection.Router.leaves (source.mapRecords_shape _)

theorem liftWing_bounded {wing : RoutingWing α ρ} {capacity : Nat}
    (bounded : RoutingBounded capacity wing) : RoutingBounded capacity (liftWing wing) := by
  cases wing with
  | none => trivial
  | some source => exact Source.Bounded.mapRecords Datum.record bounded

def Input.completePlan {t : PrefRouter α} (input : Input t ρ) : Plan α (Datum ρ) :=
  ⟨liftWing input.plan.left,liftWing input.plan.right⟩

def Input.completeHeader {t : PrefRouter α} (input : Input t ρ) : List (Datum ρ) :=
  [.header input.virtualHeader]

theorem Input.completePlan_words {t : PrefRouter α} (input : Input t ρ) :
    routingWord input.completePlan.left = (PrimaryWings.exits t).filter (·.leftOfEndpoint) ∧
      routingWord input.completePlan.right = ((PrimaryWings.exits t).filter (fun e => !e.leftOfEndpoint)).reverse := by
  simpa only [completePlan,liftWing_word] using input.plan_words

theorem Input.completePlan_bounded {t : PrefRouter α} (input : Input t ρ) :
    RoutingBounded 3 input.completePlan.left ∧ RoutingBounded 3 input.completePlan.right :=
  ⟨liftWing_bounded input.plan_bounded.1,liftWing_bounded input.plan_bounded.2⟩

def completeRepresentation (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    Source α (List (Option (Datum ρ))) :=
  expand (fun t => (inputs t).completePlan) (fun t => (inputs t).completeHeader) t

theorem completeRepresentation_bounded (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    (completeRepresentation inputs t).Bounded 5 :=
  expand_bounded _ _ 3 1 (fun t => (inputs t).completePlan_bounded) (fun _ => le_rfl) t

theorem completeRepresentation_leaves (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    (completeRepresentation inputs t).shape.leaves = t.leaves :=
  expand_leaves _ _ (fun t => (inputs t).completePlan_words.1) (fun t => (inputs t).completePlan_words.2) t

theorem completeRepresentation_root_bound (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    (completeRepresentation inputs t).rootRecord.length ≤ 1 :=
  expand_root_bound _ _ t

end TangoSquared.Paper20261030.PackedPrimary
