import MultiSplay.EndpointEmissionEmbedding
import TangoSquared.Words

/-!
# Embedding the complete initialized secondary ledger

The encoded process uses ordinary primary updates and appends its leaf depth
as the completion emission. Its rows contain the original multisplay writes
as chronological subsequences, with the same prescribed initial bits.
-/

namespace MultiSplay.Secondary

open TangoSquared (DepthTree changesFrom changesFrom_sublist)
open TangoSquared.Primary (Key)
open EndpointEncoding

/-- The chronological writes of a leaf-query process, including completion. -/
def leafRow (row : Row) (state : State) : List Key → List Bool
  | [] => []
  | leaf :: rest => (ascendingEmissions state leaf).filterMap (project row leaf) ++
      leafRow row (leafStep state leaf) rest

def leafLedger {lower upper : Nat} (hierarchy : DepthTree lower upper)
    (initial : Row → Bool) (state : State) (leaves : List Key) : Nat :=
  ∑ row ∈ rows hierarchy, changesFrom (initial row) (leafRow row state leaves)

theorem ascendingRow_sublist {height : Nat} {nodeState leafState : State}
    (aligned : Matches nodeState leafState) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height) (original : Row) :
    (ascendingRow original nodeState addresses).Sublist
      (leafRow (EndpointHierarchy.row height original) leafState (encode height nodeState addresses)) := by
  induction addresses generalizing nodeState leafState with
  | nil => exact List.Sublist.refl _
  | cons address rest ih =>
      have first := emissions_sublist aligned (inside address (by simp))
      have completed := first.trans (List.sublist_append_left _ [request height nodeState address])
      have projected := completed.filterMap (project (EndpointHierarchy.row height original)
        (request height nodeState address))
      rw [EndpointHierarchy.projected_core_emissions] at projected
      have tail := ih (step_aligned aligned height address)
        (fun key member => inside key (List.mem_cons_of_mem _ member))
      exact projected.append tail

/-- The row injection gives no multiplicity, and binary variation decreases
under deletion even with a fixed initialized bit. -/
theorem ascendingLedger_le_encoded {height : Nat} (hierarchy : DepthTree 0 height)
    (initial : Row → Bool) {nodeState leafState : State} (aligned : Matches nodeState leafState)
    {addresses : List Key} (inside : ∀ address ∈ addresses, address.length < height) :
    ascendingLedger hierarchy (fun original => initial (EndpointHierarchy.row height original)) nodeState addresses ≤
      leafLedger (EndpointHierarchy.doubled hierarchy) initial leafState (encode height nodeState addresses) := by
  have pointwise := Finset.sum_le_sum (s := rows hierarchy) (fun original _ =>
    changesFrom_sublist (ascendingRow_sublist aligned inside original) (initial (EndpointHierarchy.row height original)))
  have embedded :
      (rows hierarchy).image (EndpointHierarchy.row height) ⊆ rows (EndpointHierarchy.doubled hierarchy) := by
    intro target member
    obtain ⟨original,source,rfl⟩ := Finset.mem_image.mp member
    exact EndpointHierarchy.doubled_row_mem hierarchy source
  have sums := Finset.sum_le_sum_of_subset (f := fun row =>
    changesFrom (initial row) (leafRow row leafState (encode height nodeState addresses))) embedded
  rw [Finset.sum_image (fun a _ b _ same => EndpointHierarchy.row_injective height same)] at sums
  exact pointwise.trans sums

/-- The physical bottom-up switch order is covered by the same encoded
ledger, with the already proved linear allowance for reversing ancestors. -/
theorem actualLedger_le_encoded {height : Nat} (hierarchy : DepthTree 0 height)
    (initial : Row → Bool) {nodeState leafState : State} (aligned : Matches nodeState leafState)
    {addresses : List Key} (inside : ∀ address ∈ addresses, address.length < height) :
    actualLedger hierarchy (fun original => initial (EndpointHierarchy.row height original)) nodeState addresses ≤
      leafLedger (EndpointHierarchy.doubled hierarchy) initial leafState (encode height nodeState addresses) +
        2 * (actualHistory nodeState addresses).length := by
  have order := ledger_order_bound hierarchy (fun original => initial (EndpointHierarchy.row height original)) nodeState addresses
  have embedding := ascendingLedger_le_encoded hierarchy initial aligned inside
  omega

end MultiSplay.Secondary
