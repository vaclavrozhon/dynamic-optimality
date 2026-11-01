import MultiSplay.GlobalPreferredInventorySwitch
import MultiSplay.GlobalPreferredOnline

/-!
# Exact forest replay of the fixed online classical strategy

This replay follows the physical switches already selected by the online
strategy. Every intermediate forest is retained for the next switch and the
next request. Its work is exactly the strategy's recorded splay work.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree BST)
open TangoSquared.MTR
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest

variable {α : Type*}

theorem Switches.inventory [DecidableEq α]
    {state : State} {reference before after : RawTree α}
    {addresses : List Key} {count work : Nat}
    (run : Switches state reference addresses before after count work)
    (unique : reference.inorder.Nodup)
    (real : ∀ address ∈ addresses, referenceAt reference address ≠ .empty)
    {trees : List (RawTree α)} (inventory : Inventory state reference before trees) :
    ∃ next, Inventory (applySwitches state addresses) reference after next ∧
      SplayTrace trees
        ((schedule state addresses).flatMap fun entry => eventWord reference entry.1 entry.2)
        next work := by
  induction run generalizing trees with
  | nil => exact ⟨trees,inventory,.nil _⟩
  | cons first later ih =>
      obtain ⟨middle,middleInventory,firstTrace⟩ := first.inventory unique (real _ (by simp)) inventory
      obtain ⟨next,nextInventory,laterTrace⟩ :=
        ih unique (fun address member => real address (by simp [member])) middleInventory
      refine ⟨next,nextInventory,?_⟩
      simpa only [schedule,List.flatMap_cons] using firstTrace.append laterTrace

namespace Online

variable {n : Nat}

theorem Requests.inventory {reference : BST 0 n}
    {preference : EndpointEncoding.State} {requests : List (Fin n)}
    {before after : RawTree Nat} {count work : Nat}
    (run : Requests reference preference requests before after count work)
    {trees : List (RawTree Nat)} (inventory : Inventory preference reference.toRaw before trees) :
    ∃ next,
      Inventory ((requests.map fun request => nodeAddress reference request.val).foldl nodeStep preference)
        reference.toRaw after next ∧
      SplayTrace trees
        (historyWord reference.toRaw preference (requests.map fun request => nodeAddress reference request.val))
        next work := by
  induction run generalizing trees with
  | nil => exact ⟨trees,inventory,.nil _⟩
  | @cons preference request rest before middle after firstCount restCount firstWork restWork first later ih =>
      have unique : reference.toRaw.inorder.Nodup :=
        reference.toRaw_ordered.imp (fun h => Nat.ne_of_lt h)
      obtain ⟨middleTrees,middleInventory,firstTrace⟩ := first.inventory unique
        (fun _ member => actualEmissions_real reference (Nat.zero_le _) request.isLt preference member) inventory
      rw [actualEmissions_state] at middleInventory
      obtain ⟨next,nextInventory,laterTrace⟩ := ih middleInventory
      refine ⟨next,nextInventory,?_⟩
      exact firstTrace.append laterTrace

theorem run_preference {reference : BST 0 n} (state : State reference) (requests : List (Fin n)) :
    ((strategy reference).run state requests).1.preference =
      (requests.map fun request => nodeAddress reference request.val).foldl nodeStep state.preference := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest ih => exact ih (advance state request)

/-- The fixed online run has a replay from any persistent inventory of its
actual initial physical tree. The final inventory represents its actual
chosen final tree and preference state. -/
theorem run_inventory {reference : BST 0 n} (state : State reference) (requests : List (Fin n))
    {trees : List (RawTree Nat)}
    (inventory : Inventory state.preference reference.toRaw state.actual.toRaw trees) :
    ∃ next,
      Inventory ((strategy reference).run state requests).1.preference reference.toRaw
        ((strategy reference).run state requests).1.actual.toRaw next ∧
      SplayTrace trees
        (historyWord reference.toRaw state.preference
          (requests.map fun request => nodeAddress reference request.val))
        next (runWork state requests) := by
  obtain ⟨next,nextInventory,trace⟩ := (run_classical state requests).inventory inventory
  exact ⟨next,by rwa [run_preference],trace⟩

/-- Exact chronological splay work for the canonical initialization of the
actual classical strategy. No independently selected forest run occurs in
this statement: the cost is `runWork` of the fixed online transitions. -/
theorem initial_run_trace (reference : BST 0 n) (preference : EndpointEncoding.State)
    (requests : List (Fin n)) :
    ∃ next,
      Inventory ((strategy reference).run (initial reference preference) requests).1.preference
        reference.toRaw ((strategy reference).run (initial reference preference) requests).1.actual.toRaw next ∧
      SplayTrace (forest preference reference.toRaw)
        (historyWord reference.toRaw preference
          (requests.map fun request => nodeAddress reference request.val))
        next (runWork (initial reference preference) requests) :=
  run_inventory (initial reference preference) requests (initial_inventory preference reference.toRaw)

/-- The actual search-depth-plus-rotations cost is bounded by twice the
work of its exact persistent forest replay plus one per original request. -/
theorem initial_run_cost (reference : BST 0 n) (preference : EndpointEncoding.State)
    (requests : List (Fin n)) :
    ∃ next,
      SplayTrace (forest preference reference.toRaw)
        (historyWord reference.toRaw preference
          (requests.map fun request => nodeAddress reference request.val))
        next (runWork (initial reference preference) requests) ∧
      ((strategy reference).run (initial reference preference) requests).2 ≤
        2 * runWork (initial reference preference) requests + requests.length := by
  obtain ⟨next,inventory,trace⟩ := initial_run_trace reference preference requests
  exact ⟨next,trace,run_cost_le _ _⟩

end Online

end MultiSplay.Global.Preferred
