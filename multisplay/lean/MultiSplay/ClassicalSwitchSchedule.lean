import MultiSplay.EndpointEmissionEmbedding

/-!
# The actual switch schedule and the final root component

The existing endpoint protocol processes wrong proper ancestors in decreasing
depth and then toggles the requested node. This file exposes its intermediate
state just before that final toggle. Every proper ancestor then points toward
the requested node, so the node belongs to the root preferred path. This fact
also covers a reference leaf: its mandatory final switch is never suppressed.
-/

namespace MultiSplay.ClassicalSwitch

open ChaCha.Primary (Key branch)
open EndpointEncoding

theorem applySwitches_append (state : State) (first rest : List Key) :
    applySwitches state (first ++ rest) = applySwitches (applySwitches state first) rest := by
  induction first generalizing state with
  | nil => rfl
  | cons owner first ih => exact ih (toggle state owner)

/-- All proper reference ancestors choose the edge leading to this node. -/
def RootPreferred (state : State) (address : Key) : Prop :=
  ∀ owner side, branch owner address = some side → state owner = side

def beforeFinal (state : State) (address : Key) : State :=
  applySwitches state (ancestorEmissions state address).reverse

theorem final_toggle (state : State) (address : Key) :
    toggle (beforeFinal state address) address = nodeStep state address := by
  have complete := actualEmissions_state state address
  simpa only [actualEmissions, applySwitches_append, applySwitches, beforeFinal] using complete

theorem ancestorEmissions_not_endpoint (state : State) (address : Key) :
    address ∉ ancestorEmissions state address := by
  have unique := ascendingEmissions_nodup state address
  simp only [ascendingEmissions, List.nodup_append'] at unique
  exact fun present => List.disjoint_left.mp unique.2.2 present (by simp)

theorem beforeFinal_endpoint (state : State) (address : Key) :
    beforeFinal state address address = state address := by
  have unique : (ancestorEmissions state address).Nodup :=
    (ascendingEmissions_nodup state address).of_append_left
  have reversed : (ancestorEmissions state address).reverse.Nodup := by
    simpa only [List.nodup_reverse] using unique
  rw [beforeFinal, applySwitches_lookup state reversed]
  simp [ancestorEmissions_not_endpoint]

/-- The last switch starts in the root preferred component; this is derived
from the actual bottom-up schedule, not an additional physical hypothesis. -/
theorem beforeFinal_rootPreferred (state : State) (address : Key) :
    RootPreferred (beforeFinal state address) address := by
  intro owner side direction
  have different : owner ≠ address := by
    intro same
    subst owner
    simp [branch] at direction
  have same := congrFun (final_toggle state address) owner
  simpa [toggle, different, nodeStep, nodeWrite, direction] using same

theorem ancestor_order (state : State) (address : Key) :
    (ancestorEmissions state address).reverse.Pairwise (fun a b => b.length < a.length) := by
  simpa only [List.pairwise_reverse] using ancestorEmissions_increasing state address

theorem actualEmissions_final (state : State) (address : Key) :
    actualEmissions state address = (ancestorEmissions state address).reverse ++ [address] := rfl

theorem actualEmissions_nonempty (state : State) (address : Key) :
    actualEmissions state address ≠ [] := by simp [actualEmissions]

/-- Each switch is paired with its actual current preference state. In
particular later words may not reuse domains computed from the initial state. -/
def schedule (state : State) : List Key → List (State × Key)
  | [] => []
  | owner :: rest => (state,owner) :: schedule (toggle state owner) rest

@[simp] theorem schedule_owners (state : State) (owners : List Key) :
    (schedule state owners).map Prod.snd = owners := by
  induction owners generalizing state with
  | nil => rfl
  | cons owner rest ih => simp [schedule, ih]

theorem schedule_append (state : State) (first rest : List Key) :
    schedule state (first ++ rest) =
      schedule state first ++ schedule (applySwitches state first) rest := by
  induction first generalizing state with
  | nil => rfl
  | cons owner first ih => simp [schedule, applySwitches, ih]

/-- The current-state schedule has precisely the mandatory final switch,
with every wrong proper ancestor already corrected. -/
theorem schedule_actual (state : State) (address : Key) :
    schedule state (actualEmissions state address) =
      schedule state (ancestorEmissions state address).reverse ++ [(beforeFinal state address,address)] := by
  simp [actualEmissions, schedule_append, schedule, beforeFinal]

end MultiSplay.ClassicalSwitch
