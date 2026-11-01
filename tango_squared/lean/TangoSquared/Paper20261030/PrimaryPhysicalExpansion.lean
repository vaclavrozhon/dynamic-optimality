import TangoSquared.Paper20261030.SourcePayloadCapacity
import TangoSquared.Paper20261030.PrimaryWings

/-!
# Recursive original-key representation with bounded physical records

A plan supplies the two already projected routing wings of each primary
component. Their leaves name the actual primary exits in left-to-right
original-key order. Expand each exit with its whole child representation,
then concatenate both wings with the component's own bottom key.

If routing vertices have at most `C` source records and each component
header has at most `H` records, every physical vertex has at most
`C+1+H` records, independently of primary nesting depth. The complete
leaf word is exactly the original primary leaf word. These are static
representation results; the plan's dynamic maintenance is proved by
separate operations.
-/

namespace TangoSquared.Paper20261030.PrimaryPhysical

open PreferredProjection ColoredStorage PrimaryWings

variable {α ρ : Type*} [DecidableEq α]

abbrev RoutingWing (α ρ : Type*) := Option (Source (Exit α) (List ρ))

structure Plan (α ρ : Type*) where
  left : RoutingWing α ρ
  right : RoutingWing α ρ

def routingWord : RoutingWing α ρ → List (Exit α)
  | none => []
  | some t => t.shape.leaves

def RoutingBounded (capacity : Nat) : RoutingWing α ρ → Prop
  | none => True
  | some t => t.Bounded capacity

def graftWing (payload : Exit α → Source α (List (Option ρ))) (routing : RoutingWing α ρ) : Wing α ρ :=
  routing.map (SourcePayloads.graft payload)

theorem graftWing_bounded (payload : Exit α → Source α (List (Option ρ))) (routing : RoutingWing α ρ)
    (C H : Nat) (routingBound : RoutingBounded C routing)
    (payloadBound : ∀ e, (payload e).Bounded (C+1+H))
    (payloadRoot : ∀ e, (payload e).rootRecord.length ≤ H) :
    WingBounded (C+1+H) (graftWing payload routing) := by
  cases routing with
  | none => trivial
  | some t => exact SourcePayloads.graft_bounded payload t C H (C+1+H) routingBound payloadBound payloadRoot le_rfl

theorem graftWing_leaves (payload : Exit α → Source α (List (Option ρ))) (routing : RoutingWing α ρ) :
    wingLeaves (graftWing payload routing) = (routingWord routing).flatMap (fun e => (payload e).shape.leaves) := by
  cases routing with
  | none => rfl
  | some t => exact SourcePayloads.graft_leaves payload t

def expand (plans : PrefRouter α → Plan α ρ) (headers : PrefRouter α → List ρ)
    (t : PrefRouter α) : Source α (List (Option ρ)) :=
  let payload := fun e => if member : e ∈ exits t then expand plans headers e.subtree else .leaf t.terminal []
  component (graftWing payload (plans t).left) (graftWing payload (plans t).right) t.terminal (headers t)
termination_by t.leaves.length
decreasing_by exact exit_smaller member

theorem expand_root_bound (plans : PrefRouter α → Plan α ρ) (headers : PrefRouter α → List ρ)
    (t : PrefRouter α) : (expand plans headers t).rootRecord.length ≤ (headers t).length := by
  rw [expand]
  exact component_root_bound _ _ _ _

theorem expand_root_no_delimiter (plans : PrefRouter α → Plan α ρ) (headers : PrefRouter α → List ρ)
    (t : PrefRouter α) : none ∉ (expand plans headers t).rootRecord := by
  rw [expand]
  exact component_root_no_delimiter _ _ _ _

theorem expand_bounded (plans : PrefRouter α → Plan α ρ) (headers : PrefRouter α → List ρ)
    (C H : Nat) (planBound : ∀ t, RoutingBounded C (plans t).left ∧ RoutingBounded C (plans t).right)
    (headerBound : ∀ t, (headers t).length ≤ H) (t : PrefRouter α) :
    (expand plans headers t).Bounded (C+1+H) := by
  let payload := fun e => if member : e ∈ exits t then expand plans headers e.subtree else .leaf t.terminal []
  have payloadBound : ∀ e, (payload e).Bounded (C+1+H) := by
    intro e
    dsimp only [payload]
    split
    · exact expand_bounded plans headers C H planBound headerBound e.subtree
    · exact Nat.zero_le _
  have payloadRoot : ∀ e, (payload e).rootRecord.length ≤ H := by
    intro e
    dsimp only [payload]
    split
    · exact (expand_root_bound plans headers e.subtree).trans (headerBound e.subtree)
    · exact Nat.zero_le _
  rw [expand]
  apply component_bounded
  · exact graftWing_bounded payload _ C H (planBound t).1 payloadBound payloadRoot
  · exact graftWing_bounded payload _ C H (planBound t).2 payloadBound payloadRoot
  · have := headerBound t; omega
termination_by t.leaves.length
decreasing_by exact exit_smaller (by assumption)

theorem expand_leaves (plans : PrefRouter α → Plan α ρ) (headers : PrefRouter α → List ρ)
    (leftWord : ∀ t, routingWord (plans t).left = (exits t).filter (·.leftOfEndpoint))
    (rightWord : ∀ t, routingWord (plans t).right = ((exits t).filter (fun e => !e.leftOfEndpoint)).reverse)
    (t : PrefRouter α) : (expand plans headers t).shape.leaves = t.leaves := by
  let payload := fun e => if member : e ∈ exits t then expand plans headers e.subtree else .leaf t.terminal []
  have words : ∀ e ∈ exits t, (payload e).shape.leaves = e.subtree.leaves := by
    intro e he
    dsimp only [payload]
    rw [dif_pos he]
    exact expand_leaves plans headers leftWord rightWord e.subtree
  rw [expand,component_leaves,graftWing_leaves,graftWing_leaves,leftWord,rightWord]
  have hl := List.flatMap_congr (l := (exits t).filter (·.leftOfEndpoint))
    (f := fun e => (payload e).shape.leaves) (g := fun e => e.subtree.leaves)
    (fun e he => words e (List.mem_filter.mp he).1)
  have hr := List.flatMap_congr (l := ((exits t).filter (fun e => !e.leftOfEndpoint)).reverse)
    (f := fun e => (payload e).shape.leaves) (g := fun e => e.subtree.leaves)
    (fun e he => words e (List.mem_filter.mp (List.mem_reverse.mp he)).1)
  rw [hl,hr]
  exact (leaf_partition t).symm
termination_by t.leaves.length
decreasing_by exact exit_smaller (by assumption)

end TangoSquared.Paper20261030.PrimaryPhysical
