import Greedy.InstanceCuts

/-! Old frozen-instance properties survive actual comparator preparation. -/

namespace Greedy.ClosedInstances

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem detachAll_closed {n id : ℕ} {property : Frozen → Prop} (before : BST 0 n)
    (key start : ℕ) (states : HeapSides n) (closed : HeapClosed id property states)
    (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (detachAll before key (conversionNames start) (conversionNames start) states) := by
  let selected := fun (owner : External n) (side : Bool) => growerHasKey key (states owner side)
  let converted := (convertHeap before.externalDepth selected start states).1
  have convertedClosed := convertHeap_closed id start property before.externalDepth selected states closed past
  apply heap_old_descendants convertedClosed hereditary (fun owner side => GrowthJournal.detachAll_grower before key start states owner side)
  intro owner side block member same
  have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side = eraseFrozenKey key (converted owner side) := by
    dsimp only [converted]
    rw [convertHeap_apply]
    rfl
  rw [equal] at member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, same, erase_descends old key⟩

theorem detachPorts_closed {n id : ℕ} {property : Frozen → Prop} (before : BST 0 n)
    (start : ℕ) (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (closed : HeapClosed id property states) (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => exact closed
  | cons key rest ih =>
      exact ih (stage+1) _ (detachAll_closed before key (start + Fintype.card (Place n)*stage) states closed hereditary
        (past.trans_le (Nat.le_add_right _ _)))

theorem preparation_closed {n id : ℕ} {property : Frozen → Prop} (before after : BST 0 n)
    (start : ℕ) (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n)
    (closed : HeapClosed id property states) (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (preparedForCuts before after start ports owners states) := by
  classical
  have grown := convertHeap_closed id start property before.externalDepth
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) states closed past
  rw [← prepareAllGrowers_fresh_eq] at grown
  have detached := detachPorts_closed before start ports 1 _ grown hereditary past
  have sealed := convertHeap_closed id (start + Fintype.card (Place n)*(ports.length+1)) property before.externalDepth
    (fun owner _ => decide (owner ∈ owners)) _ detached (past.trans_le (Nat.le_add_right _ _))
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, sequenceNames, Nat.mul_zero, Nat.add_zero] using sealed

theorem allocated_preparation_closed {n id depth : ℕ} {property : Frozen → Prop} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (closed : HeapClosed id property states)
    (hereditary : ClosedFamilies.Hereditary property) (past : id < start) :
    HeapClosed id property (allocateComparatorPreparation profile ports owners start states).states := by
  apply allocateCuts_closed profile.entries _ _ (preparation_closed before after start ports owners states closed hereditary past) hereditary
  exact past.trans_le (Nat.le_add_right _ _)

end Greedy.ClosedInstances
