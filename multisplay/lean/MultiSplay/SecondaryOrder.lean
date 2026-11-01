import MultiSplay.SecondaryRows
import MultiSplay.SwitchEmissions

/-!
# The secondary ledger in the actual multi-splay switch order

Rows are indexed by a secondary depth interval and its primary owner. Each
query writes its ancestor emissions in reverse order and then writes its final
node depth. The increasing-order ledger uses the same rows and the same initial
bits. Their difference is charged to the number of ancestor emissions, with no
factor for hierarchy height or number of primary owners.
-/

namespace MultiSplay.Secondary

open TangoSquared (DepthTree changesFrom)
open TangoSquared.Primary (Key)

def ascendingCount {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (queries : List Query) : Nat :=
  ∑ row ∈ rows hierarchy, changesFrom (initial row)
    (queries.flatMap (fun query => query.ancestorWrites row ++ query.finalWrites row))

def actualCount {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (queries : List Query) : Nat :=
  ∑ row ∈ rows hierarchy, changesFrom (initial row)
    (queries.flatMap (fun query => (query.ancestorWrites row).reverse ++ query.finalWrites row))

theorem actual_le_ascending {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (queries : List Query) :
    actualCount hierarchy initial queries ≤ ascendingCount hierarchy initial queries +
      2 * (queries.map (fun query => query.ancestors.length-1)).sum := by
  have bound := rows_order_bound (rows hierarchy) queries initial
    (fun row query => query.ancestorWrites row) (fun row query => query.finalWrites row)
  have charges : (queries.map (fun query => ∑ row ∈ rows hierarchy, if Mixed (query.ancestorWrites row) then 1 else 0)).sum ≤
      (queries.map (fun query => query.ancestors.length-1)).sum := by
    clear bound
    induction queries with
    | nil => rfl
    | cons query rest ih => exact Nat.add_le_add (query_rows_bound hierarchy query) ih
  change actualCount hierarchy initial queries ≤ ascendingCount hierarchy initial queries + _ at bound
  omega

def Query.reverseAncestors (query : Query) : Query := ⟨query.address,query.ancestors.reverse⟩

theorem Query.reverse_writes (query : Query) (row : Row) :
    query.reverseAncestors.ancestorWrites row = (query.ancestorWrites row).reverse := by
  by_cases owner : row.2 = query.address.take row.1.lo <;>
    simp [reverseAncestors, ancestorWrites, depthWord, owner, List.filterMap_reverse]

theorem Query.reverse_final (query : Query) (row : Row) :
    query.reverseAncestors.finalWrites row = query.finalWrites row := rfl

theorem Query.reverse_length (query : Query) :
    query.reverseAncestors.ancestors.length = query.ancestors.length := List.length_reverse

theorem ascending_le_actual {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (queries : List Query) :
    ascendingCount hierarchy initial queries ≤ actualCount hierarchy initial queries +
      2 * (queries.map (fun query => query.ancestors.length-1)).sum := by
  have bound := actual_le_ascending hierarchy initial (queries.map Query.reverseAncestors)
  simpa only [actualCount, ascendingCount, List.flatMap_map, List.map_map, Function.comp_def,
    Query.reverse_writes, List.reverse_reverse, Query.reverse_final, Query.reverse_length] using bound

/-- These are the actual adaptive emissions of the existing preference
protocol, including its mandatory final toggle at every request. -/
def endpointQueries (state : EndpointEncoding.State) : List Key → List Query
  | [] => []
  | address::rest => ⟨address,(EndpointEncoding.ancestorEmissions state address).map List.length⟩ ::
      endpointQueries (EndpointEncoding.nodeStep state address) rest

theorem endpoint_credits_le_switches (state : EndpointEncoding.State) (addresses : List Key) :
    ((endpointQueries state addresses).map (fun query => query.ancestors.length-1)).sum ≤
      (EndpointEncoding.actualHistory state addresses).length := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address rest ih =>
      have tail := ih (EndpointEncoding.nodeStep state address)
      simp only [endpointQueries, List.map_cons, List.sum_cons, List.length_map,
        EndpointEncoding.actualHistory, EndpointEncoding.actualEmissions, List.length_append,
        List.length_reverse, List.length_singleton]
      omega

/-- The actual-order secondary count is at most the analytical increasing
count plus twice the actual primary-switch count. This applies to every binary
interval hierarchy and to arbitrary initial secondary bits. -/
theorem actual_order_bound {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (state : EndpointEncoding.State) (addresses : List Key) :
    actualCount hierarchy initial (endpointQueries state addresses) ≤
      ascendingCount hierarchy initial (endpointQueries state addresses) +
        2 * (EndpointEncoding.actualHistory state addresses).length := by
  have bound := actual_le_ascending hierarchy initial (endpointQueries state addresses)
  have credits := endpoint_credits_le_switches state addresses
  omega

end MultiSplay.Secondary
