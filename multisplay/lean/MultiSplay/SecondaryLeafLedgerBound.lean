import MultiSplay.SecondaryTerminalRows
import MultiSplay.IntervalLowerBound

/-!
# The initialized secondary leaf ledger and the dynamic lower counter

All terms refer to the concrete leaf preference process. The first-head
allowance is restricted to left-writing rows, and the joint reset budget is
paid by initialized primary flips.
-/

namespace MultiSplay.Secondary

open TangoSquared (DepthTree Gadget changesFrom)
open TangoSquared.Primary
open EndpointEncoding

theorem rowGadget_injective : Function.Injective rowGadget := by
  rintro ⟨a,u⟩ ⟨b,v⟩ same
  have intervals : a = b := congrArg Gadget.split same
  have owners : u = v := congrArg Gadget.owner same
  subst b; subst v
  rfl

theorem rows_image_gadgets {height : Nat} (hierarchy : DepthTree 0 height) :
    (rows hierarchy).image rowGadget = IntervalLower.allGadgets hierarchy := by
  ext gadget
  rw [IntervalLower.mem_allGadgets]
  constructor
  · intro member
    obtain ⟨row,valid,rfl⟩ := Finset.mem_image.mp member
    obtain ⟨splitMember,ownerMember⟩ := Finset.mem_sigma.mp valid
    have length := (mem_level _ _).mp ownerMember
    have bounds := hierarchy.node_bounds splitMember
    exact ⟨splitMember,(mem_owners _ _).mpr (by change row.2.length < height; omega),length⟩
  · rintro ⟨splitMember,_,length⟩
    exact Finset.mem_image.mpr ⟨⟨gadget.split,gadget.owner⟩,
      Finset.mem_sigma.mpr ⟨splitMember,(mem_level _ _).mpr length⟩,by cases gadget; rfl⟩

theorem sum_row_demands {height : Nat} (hierarchy : DepthTree 0 height) (leaves : List Key) :
    (∑ row ∈ rows hierarchy, if row.1.hi < height then (rowGadget row).count leaves else 0) =
      IntervalLower.secondaryDemands hierarchy leaves := by
  rw [IntervalLower.secondaryDemands,IntervalLower.gadgets,Finset.sum_filter,← rows_image_gadgets,
    Finset.sum_image (fun _ _ _ _ same => rowGadget_injective same)]
  rfl

theorem leafLedger_bound {height : Nat} (hierarchy : DepthTree 0 height) (state : State)
    (leaves : List Key) (heights : ∀ leaf ∈ leaves, leaf.length = height) :
    leafLedger hierarchy (fun _ => true) state leaves ≤
      2*IntervalLower.secondaryDemands hierarchy leaves + 2*leafCost height state leaves +
        3*((rows hierarchy).filter (fun row => false ∈ leafRow row state leaves)).card := by
  have bounds : ∀ row ∈ rows hierarchy,
      changesFrom true (leafRow row state leaves) ≤
        2*(if row.1.hi < height then (rowGadget row).count leaves else 0) +
        2*rowResets row state leaves + 3*(if false ∈ leafRow row state leaves then 1 else 0) := by
    intro row member
    obtain ⟨splitMember,ownerMember⟩ := Finset.mem_sigma.mp member
    have interval := hierarchy.node_bounds splitMember
    exact initialized_row_bound ((mem_level _ _).mp ownerMember) interval.2.1 interval.2.2.1
      interval.2.2.2 state leaves heights
  have sums := Finset.sum_le_sum bounds
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,sum_row_demands,Finset.sum_boole] at sums
  have resets := reset_history_budget hierarchy state leaves heights
  change leafLedger hierarchy (fun _ => true) state leaves ≤
    2*IntervalLower.secondaryDemands hierarchy leaves +
    2*(∑ row ∈ rows hierarchy,rowResets row state leaves) +
    3*((rows hierarchy).filter (fun row => false ∈ leafRow row state leaves)).card at sums
  omega

theorem encoded_leafLedger_bound {height : Nat} (hierarchy : DepthTree 0 (2*height))
    {leafState : State} (right : RightOutside height leafState) (nodeState : State) {addresses : List Key}
    (inside : ∀ address ∈ addresses, address.length < height) :
    leafLedger hierarchy (fun _ => true) leafState (encode height nodeState addresses) ≤
      2*IntervalLower.secondaryDemands hierarchy (encode height nodeState addresses) +
        2*TangoSquared.primaryCount (2*height) (encode height nodeState addresses) + 18*(2^height-1) := by
  have ledger := leafLedger_bound hierarchy leafState (encode height nodeState addresses) (encode_on_leaves nodeState inside)
  have primary := encoded_leafCost_le_primary right nodeState inside
  have support := encoded_left_rows_card hierarchy right nodeState inside
  omega

end MultiSplay.Secondary
