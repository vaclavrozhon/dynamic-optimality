import ChaCha.Paper20261030.PackedPrimaryPlan

/-!
# Bounded complete primary representations from actual depth trees

An input is a source tree whose ordered leaves are the genuine exit depths,
the completion depth, and optionally the dormant sentinel. Its shape and
records are unrestricted here. Packing and recursively attaching the actual
exit components produces exactly the original ordered keys, with at most
sixteen records per physical vertex. The bound includes attachment markers
and the virtual headers of nested components.
-/

namespace ChaCha.Paper20261030.PackedPrimary

open PreferredProjection ColoredStorage PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

structure Input (t : PrefRouter α) (ρ : Type*) where
  start : Nat
  source : Source Nat ρ
  leaves : source.shape.leaves = List.range' start ((exits t).length + 1) ∨
    (0 < start ∧ source.shape.leaves = (start-1) :: List.range' start ((exits t).length + 1))

theorem Input.ports {t : PrefRouter α} (input : Input t ρ) :
    input.source.shape.leaves.filterMap (portAt input.start (exits t)) = exits t := by
  rcases input.leaves with completed | ⟨positive,dormant⟩
  · rw [completed,portAt_completed_word]
  · rw [dormant,List.filterMap_cons,portAt_sentinel positive,portAt_completed_word]

theorem Input.size {t : PrefRouter α} (input : Input t ρ) :
    input.source.shape.leaves.length ≤ (exits t).length + 2 := by
  rcases input.leaves with completed | ⟨_,dormant⟩
  · rw [completed,List.length_range']; omega
  · rw [dormant,List.length_cons,List.length_range']

def Input.plan {t : PrefRouter α} (input : Input t ρ) : Plan α ρ :=
  PackedPrimary.plan input.start t input.source

def Input.header {t : PrefRouter α} (input : Input t ρ) : List ρ :=
  PackedPrimary.header input.start t input.source

theorem Input.plan_words {t : PrefRouter α} (input : Input t ρ) :
    routingWord input.plan.left = (exits t).filter (·.leftOfEndpoint) ∧
      routingWord input.plan.right = ((exits t).filter (fun e => !e.leftOfEndpoint)).reverse :=
  PackedPrimary.plan_words input.start t input.source input.ports

theorem Input.plan_bounded {t : PrefRouter α} (input : Input t ρ) :
    RoutingBounded 3 input.plan.left ∧ RoutingBounded 3 input.plan.right :=
  PackedPrimary.plan_bounded input.start t input.source

theorem Input.header_bounded {t : PrefRouter α} (input : Input t ρ) :
    input.header.length ≤ 12 :=
  header_bound input.start t input.source input.ports input.size

def representation (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    Source α (List (Option ρ)) :=
  expand (fun t => (inputs t).plan) (fun t => (inputs t).header) t

theorem representation_bounded (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    (representation inputs t).Bounded 16 :=
  expand_bounded _ _ 3 12 (fun t => (inputs t).plan_bounded) (fun t => (inputs t).header_bounded) t

theorem representation_root_bounded (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    (representation inputs t).rootRecord.length ≤ 12 :=
  (expand_root_bound _ _ t).trans (inputs t).header_bounded

theorem representation_leaves (inputs : (t : PrefRouter α) → Input t ρ) (t : PrefRouter α) :
    (representation inputs t).shape.leaves = t.leaves :=
  expand_leaves _ _ (fun t => (inputs t).plan_words.1) (fun t => (inputs t).plan_words.2) t

end ChaCha.Paper20261030.PackedPrimary
