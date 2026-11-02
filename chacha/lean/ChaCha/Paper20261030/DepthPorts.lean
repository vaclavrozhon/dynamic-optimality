import ChaCha.Paper20261030.PrimaryWings
import ChaCha.Paper20261030.PreferredPathSizes

/-!
# Replacing depth leaves by primary exit ports

A component starting at primary depth `start` has one exit port for each
internal vertex of its preferred path. The next depth is its completion
leaf. A dormant component also has a sentinel at `start - 1`. Neither
completion nor sentinel represents an original-key subtree. The map below
deletes these two administrative leaves and replaces every genuine depth
by its actual exit. Its correctness is independent of the routing shape.
-/

namespace ChaCha.Paper20261030.PrimaryWings

open RouterProjection PreferredProjection

variable {α β : Type*}

theorem exits_length (t : PrefRouter α) : (exits t).length = t.rootInternal := by
  induction t with
  | leaf key => rfl
  | fork bit l r ihl ihr =>
    cases bit <;> simp [exits, PrefRouter.rootInternal, ihl, ihr]

theorem perfect_exits_length {h : Nat} {t : PrefRouter α} (ht : t.Perfect h) :
    (exits t).length = h := by
  rw [exits_length, PrefRouter.perfect_rootInternal ht]

def portAt (start : Nat) (ports : List β) (depth : Nat) : Option β :=
  if start ≤ depth then ports[depth - start]? else none

theorem filterMap_range_lookup (ports : List β) :
    (List.range ports.length).filterMap (fun i => ports[i]?) = ports := by
  induction ports with
  | nil => rfl
  | cons a ports ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.filterMap_cons,
      List.getElem?_cons_zero, List.filterMap_map,
      List.cons.injEq, true_and]
    exact ih

theorem portAt_word (start : Nat) (ports : List β) :
    (List.range' start ports.length).filterMap (portAt start ports) = ports := by
  rw [List.range'_eq_map_range, List.filterMap_map]
  simpa [Function.comp_def, portAt] using filterMap_range_lookup ports

@[simp] theorem portAt_completion (start : Nat) (ports : List β) :
    portAt start ports (start + ports.length) = none := by
  simp [portAt]

theorem portAt_sentinel {start : Nat} (hs : 0 < start) (ports : List β) :
    portAt start ports (start - 1) = none := by
  simp [portAt, show ¬start ≤ start - 1 by omega]

theorem portAt_completed_word (start : Nat) (ports : List β) :
    (List.range' start (ports.length + 1)).filterMap (portAt start ports) = ports := by
  rw [← List.range'_append_1, List.filterMap_append, portAt_word]
  simp [List.range']

def depthPorts (start : Nat) (ports : List β) (routing : Router Nat) : Router β :=
  Paper20261030.Router.substitute
    (fun d => match portAt start ports d with
      | none => .empty
      | some port => .leaf port) routing

theorem depthPorts_leaves (start : Nat) (ports : List β) (routing : Router Nat) :
    (depthPorts start ports routing).leaves = routing.leaves.filterMap (portAt start ports) := by
  rw [depthPorts, substitute_leaves]
  induction routing.leaves with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.flatMap_cons, List.filterMap_cons]
    cases portAt start ports d <;> simp [Router.leaves, ih]

theorem depthPorts_completed (start : Nat) (ports : List β) (routing : Router Nat)
    (hr : routing.leaves = List.range' start (ports.length + 1)) :
    (depthPorts start ports routing).leaves = ports := by
  rw [depthPorts_leaves, hr, portAt_completed_word]

theorem depthPorts_dormant {start : Nat} (hs : 0 < start) (ports : List β)
    (routing : Router Nat)
    (hr : routing.leaves = (start - 1) :: List.range' start (ports.length + 1)) :
    (depthPorts start ports routing).leaves = ports := by
  rw [depthPorts_leaves, hr, List.filterMap_cons, portAt_sentinel hs]
  exact portAt_completed_word start ports

theorem completed_component_leaves (start : Nat) (t : PrefRouter α) (routing : Router Nat)
    (hr : routing.leaves = List.range' start ((exits t).length + 1))
    (payload : Exit α → Router α)
    (hp : ∀ e ∈ exits t, (payload e).leaves = e.subtree.leaves) :
    (component (depthPorts start (exits t) routing) t.terminal payload).leaves = t.leaves :=
  component_leaves t _ (depthPorts_completed start (exits t) routing hr) payload hp

theorem dormant_component_leaves {start : Nat} (hs : 0 < start)
    (t : PrefRouter α) (routing : Router Nat)
    (hr : routing.leaves = (start - 1) :: List.range' start ((exits t).length + 1))
    (payload : Exit α → Router α)
    (hp : ∀ e ∈ exits t, (payload e).leaves = e.subtree.leaves) :
    (component (depthPorts start (exits t) routing) t.terminal payload).leaves = t.leaves :=
  component_leaves t _ (depthPorts_dormant hs (exits t) routing hr) payload hp

end ChaCha.Paper20261030.PrimaryWings
