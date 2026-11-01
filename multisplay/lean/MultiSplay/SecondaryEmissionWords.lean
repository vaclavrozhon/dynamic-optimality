import MultiSplay.SecondaryOrder

/-!
# Literal owner-row words of the multi-splay emission history

The projection uses the queried node's ancestor at the interval's lower depth.
It records only emissions whose depths belong to that interval. The following
identities connect the order comparison to the existing adaptive preference
protocol, rather than to a separately supplied list of query blocks.
-/

namespace MultiSplay.Secondary

open TangoSquared (DepthTree changesFrom)
open TangoSquared.Primary (Key)
open EndpointEncoding (State ancestorEmissions ascendingEmissions actualEmissions nodeStep actualHistory)

def project (row : Row) (address emitted : Key) : Option Bool :=
  if row.2 = address.take row.1.lo then
    if row.1.lo ≤ emitted.length ∧ emitted.length ≤ row.1.hi then some (decide (row.1.cut < emitted.length)) else none
  else none

theorem actual_emission_block (state : State) (address : Key) (row : Row) :
    (actualEmissions state address).filterMap (project row address) =
      ((⟨address,(ancestorEmissions state address).map List.length⟩ : Query).ancestorWrites row).reverse ++
      (⟨address,(ancestorEmissions state address).map List.length⟩ : Query).finalWrites row := by
  by_cases owner : row.2 = address.take row.1.lo <;>
    simp [actualEmissions, project, Query.ancestorWrites, Query.finalWrites, depthWord,
      owner, List.filterMap_append, List.filterMap_reverse, List.filterMap_map] <;> rfl

theorem ascending_emission_block (state : State) (address : Key) (row : Row) :
    (ascendingEmissions state address).filterMap (project row address) =
      (⟨address,(ancestorEmissions state address).map List.length⟩ : Query).ancestorWrites row ++
      (⟨address,(ancestorEmissions state address).map List.length⟩ : Query).finalWrites row := by
  by_cases owner : row.2 = address.take row.1.lo <;>
    simp [ascendingEmissions, project, Query.ancestorWrites, Query.finalWrites, depthWord,
      owner, List.filterMap_append, List.filterMap_map] <;> rfl

def actualRow (row : Row) (state : State) : List Key → List Bool
  | [] => []
  | address::rest => (actualEmissions state address).filterMap (project row address) ++ actualRow row (nodeStep state address) rest

def ascendingRow (row : Row) (state : State) : List Key → List Bool
  | [] => []
  | address::rest => (ascendingEmissions state address).filterMap (project row address) ++ ascendingRow row (nodeStep state address) rest

theorem actualRow_eq (row : Row) (state : State) (addresses : List Key) :
    actualRow row state addresses = (endpointQueries state addresses).flatMap
      (fun query => (query.ancestorWrites row).reverse++query.finalWrites row) := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address rest ih => simp only [actualRow, endpointQueries, List.flatMap_cons, actual_emission_block, ih]

theorem ascendingRow_eq (row : Row) (state : State) (addresses : List Key) :
    ascendingRow row state addresses = (endpointQueries state addresses).flatMap
      (fun query => query.ancestorWrites row++query.finalWrites row) := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address rest ih => simp only [ascendingRow, endpointQueries, List.flatMap_cons, ascending_emission_block, ih]

/-- The actual secondary ledger, summed over persistent owner rows. -/
def actualLedger {lower upper : Nat} (hierarchy : DepthTree lower upper) (initial : Row → Bool)
    (state : State) (addresses : List Key) : Nat :=
  ∑ row ∈ rows hierarchy, changesFrom (initial row) (actualRow row state addresses)

def ascendingLedger {lower upper : Nat} (hierarchy : DepthTree lower upper) (initial : Row → Bool)
    (state : State) (addresses : List Key) : Nat :=
  ∑ row ∈ rows hierarchy, changesFrom (initial row) (ascendingRow row state addresses)

theorem ledger_order_bound {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (state : State) (addresses : List Key) :
    actualLedger hierarchy initial state addresses ≤ ascendingLedger hierarchy initial state addresses +
      2 * (actualHistory state addresses).length := by
  simpa only [actualLedger, ascendingLedger, actualRow_eq, ascendingRow_eq, actualCount, ascendingCount] using
    actual_order_bound hierarchy initial state addresses

theorem ledger_order_reverse_bound {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (state : State) (addresses : List Key) :
    ascendingLedger hierarchy initial state addresses ≤ actualLedger hierarchy initial state addresses +
      2 * (actualHistory state addresses).length := by
  have bound := ascending_le_actual hierarchy initial (endpointQueries state addresses)
  have credits := endpoint_credits_le_switches state addresses
  simp only [actualLedger, ascendingLedger, actualRow_eq, ascendingRow_eq]
  change ascendingCount hierarchy initial (endpointQueries state addresses) ≤
    actualCount hierarchy initial (endpointQueries state addresses) + _
  omega

end MultiSplay.Secondary
