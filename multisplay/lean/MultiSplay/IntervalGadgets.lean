import MultiSplay.IntervalWitnesses
import ChaCha.GadgetAggregation

/-! # Concrete owner gadgets of an arbitrary binary interval hierarchy -/

namespace MultiSplay.IntervalLower

open ChaCha
open ChaCha.Primary

def allGadgets {H : Nat} (hierarchy : DepthTree 0 H) : Finset Gadget :=
  ((hierarchy.nodes ×ˢ owners H).filter (fun pair => pair.2.length = pair.1.lo)).image
    (fun pair => ⟨pair.1,pair.2⟩)

def gadgets {H : Nat} (hierarchy : DepthTree 0 H) : Finset Gadget :=
  (allGadgets hierarchy).filter (fun gadget => gadget.split.hi < H)

def secondaryDemands {H : Nat} (hierarchy : DepthTree 0 H) (word : List Key) : Nat :=
  ∑ gadget ∈ gadgets hierarchy, gadget.count word

theorem mem_allGadgets {H : Nat} {hierarchy : DepthTree 0 H} {gadget : Gadget} :
    gadget ∈ allGadgets hierarchy ↔ gadget.split ∈ hierarchy.nodes ∧
      gadget.owner ∈ owners H ∧ gadget.owner.length = gadget.split.lo := by
  cases gadget
  simp [allGadgets, and_assoc]

theorem mem_gadgets {H : Nat} {hierarchy : DepthTree 0 H} {gadget : Gadget} :
    gadget ∈ gadgets hierarchy ↔ gadget.split ∈ hierarchy.nodes ∧
      gadget.owner ∈ owners H ∧ gadget.owner.length = gadget.split.lo ∧ gadget.split.hi < H := by
  simp only [gadgets, Finset.mem_filter, mem_allGadgets, and_assoc]

theorem allGadgets_valid {H : Nat} {hierarchy : DepthTree 0 H} {gadget : Gadget}
    (member : gadget ∈ allGadgets hierarchy) : Valid hierarchy gadget :=
  ⟨(mem_allGadgets.mp member).1,(mem_allGadgets.mp member).2.2⟩

theorem gadgets_subset_all {H : Nat} (hierarchy : DepthTree 0 H) : gadgets hierarchy ⊆ allGadgets hierarchy :=
  Finset.filter_subset _ _

theorem fragment_potential_telescope_primary {H : Nat} (hierarchy : DepthTree 0 H) (word : List Key)
    (leaves : OnLeaves H word) :
    (∑ split ∈ hierarchy.nodes, splitPotentialDifference H word split) + fragmentPotential H word 0 H =
      (cyclicPrimary H word : Int) := by
  have telescope := hierarchy.potential_telescope (fragmentPotential H word)
  rw [binary_leaf_potential H word leaves] at telescope
  exact telescope

end MultiSplay.IntervalLower
