import Greedy.FamilyStructural

/-! Family freshness through the literal comparator preparation program. -/

namespace Greedy.FamilyNames

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem detachAll_inventory {n : ℕ} (before : BST 0 n) (key start : ℕ) (states : HeapSides n)
    (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (detachAll before key (conversionNames start) (conversionNames start) states)
      (start + Fintype.card (Place n)) := by
  let selected := fun (owner : External n) (side : Bool) => growerHasKey key (states owner side)
  let converted := (convertHeap before.externalDepth selected start states).1
  have convertedInv := convertHeap_inventory before.externalDepth selected start states inventory
  apply heap_descendants convertedInv (after := detachAll before key (conversionNames start) (conversionNames start) states)
    (fun owner side => GrowthJournal.detachAll_grower before key start states owner side)
  intro owner side block member
  have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side =
      eraseFrozenKey key (converted owner side) := by
    dsimp only [converted]
    rw [convertHeap_apply]
    rfl
  rw [equal] at member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, erase_descends old key⟩

theorem detachPorts_inventory {n : ℕ} (before : BST 0 n) (start : ℕ)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (inventory : HeapFamilyInventory states (start + Fintype.card (Place n)*stage)) :
    HeapFamilyInventory (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1
      (start + Fintype.card (Place n)*(stage+ports.length)) := by
  induction ports generalizing stage states with
  | nil => simpa only [List.length_nil, Nat.add_zero, detachPorts] using inventory
  | cons key rest ih =>
      have head := detachAll_inventory before key (start + Fintype.card (Place n)*stage) states inventory
      have step : HeapFamilyInventory
          (detachAll before key (sequenceNames start stage) (sequenceNames start stage) states)
          (start + Fintype.card (Place n)*(stage+1)) := by
        simpa only [sequenceNames, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using head
      have tail := ih (stage+1) _ step
      simpa only [detachPorts, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

theorem preparation_inventory {n : ℕ} (before after : BST 0 n) (start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n)
    (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (preparedForCuts before after start ports owners states)
      (start + Fintype.card (Place n)*(ports.length+2)) := by
  classical
  let names := sequenceNames (n:=n) start
  let growing := prepareAllGrowers before after (names 0) (names 0) states
  let detached := (detachPorts before names names ports 1 growing).1
  have grown : HeapFamilyInventory growing (start + Fintype.card (Place n)*1) := by
    have converted := convertHeap_inventory before.externalDepth
      (fun owner side => decide (GrowerMismatch before after owner (states owner side))) start states inventory
    rw [← prepareAllGrowers_fresh_eq] at converted
    simpa only [growing, names, sequenceNames, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using converted
  have removed := detachPorts_inventory before start ports 1 growing grown
  have sealed := convertHeap_inventory before.externalDepth (fun owner _ => decide (owner ∈ owners))
    (start + Fintype.card (Place n)*(ports.length+1)) detached (by simpa only [Nat.add_comm] using removed)
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, names, sequenceNames, Nat.mul_add, Nat.mul_two, Nat.mul_one,
    Nat.add_assoc, growing, detached] using sealed

theorem allocated_preparation_inventory {n depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (inventory : HeapFamilyInventory states start) :
    HeapFamilyInventory (allocateComparatorPreparation profile ports owners start states).states
      (allocateComparatorPreparation profile ports owners start states).next :=
  allocateCuts_inventory profile.entries _ _ (preparation_inventory before after start ports owners states inventory)

end Greedy.FamilyNames
