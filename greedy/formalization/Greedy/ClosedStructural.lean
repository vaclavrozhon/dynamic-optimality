import Greedy.ClosedFamilies
import Greedy.GrowthStructural

/-! Closed-family hereditary properties survive cuts, moves, and rebasing. -/

namespace Greedy.ClosedFamilies

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation

theorem heap_inherited {n family : ℕ} {property : Frozen → Prop} {before after : HeapSides n}
    (closed : HeapClosed family property before) (hereditary : Hereditary property)
    (growers : ∀ owner side, (after owner side).grower = (before owner side).grower)
    (fragments : ∀ owner side block, block ∈ (after owner side).shrinking →
      ∃ oldOwner oldSide old, old ∈ (before oldOwner oldSide).shrinking ∧ Descends block old) :
    HeapClosed family property after := by
  apply closed.inherited hereditary
  · intro slot grower present
    exact ⟨slot, grower, (growers _ _).symm.trans present, rfl⟩
  · intro slot block member
    obtain ⟨oldOwner, oldSide, old, oldMem, descendant⟩ := fragments _ _ block member
    exact ⟨encode n (oldOwner, oldSide), old, by simpa [table] using oldMem, descendant⟩

theorem allocateCuts_closed {n family : ℕ} {property : Frozen → Prop} (cuts : List (ℕ × ℕ))
    (start : ℕ) (states : HeapSides n) (closed : HeapClosed family property states) (hereditary : Hereditary property) :
    HeapClosed family property (allocateCuts cuts start states).states := by
  apply heap_inherited closed hereditary (GrowthJournal.allocateCuts_grower cuts start states)
  intro owner side block member
  have equal := congrArg Prod.fst (allocateCuts_eq cuts start states)
  dsimp only at equal
  rw [← equal] at member
  obtain ⟨old, oldMem, descendant⟩ := prepareCuts_descends (allocateCuts cuts start states).names cuts 0 states owner side block member
  exact ⟨owner, side, old, oldMem, descendant⟩

theorem rebase_closed {n family : ℕ} {property : Frozen → Prop} (before after : BST 0 n)
    (states : HeapSides n) (closed : HeapClosed family property states) (hereditary : Hereditary property) :
    HeapClosed family property (rebaseAll before after states) := by
  apply heap_inherited closed hereditary (after := rebaseAll before after states) (fun _ _ => rfl)
  intro owner side block member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, rfl, rfl, List.Sublist.refl _⟩

theorem junction_closed {n family : ℕ} {property : Frozen → Prop}
    (oldOwner newOwner : External n) (lo hi start : ℕ) (states : HeapSides n)
    (closed : HeapClosed family property states) (hereditary : Hereditary property) :
    HeapClosed family property (allocateJunction oldOwner newOwner lo hi start states).states := by
  apply heap_inherited closed hereditary (GrowthJournal.junction_grower oldOwner newOwner lo hi start states)
  intro owner side block member
  rw [allocateJunction_eq] at member
  unfold moveJunction at member
  split_ifs at member with old new
  · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
      (states oldOwner side) block (List.mem_append_left _ member)
    exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · change block ∈ (states newOwner side).shrinking ++ _ at member
    rcases List.mem_append.mp member with own | moved
    · exact ⟨newOwner, side, block, own, descends_refl _⟩
    · obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side (junctionCut side lo hi) _
        (states oldOwner side) block (List.mem_append_right _ moved)
      exact ⟨oldOwner, side, original, originalMem, descendant⟩
  · exact ⟨owner, side, block, member, descends_refl _⟩

theorem detachAll_closed {n family : ℕ} {property : Frozen → Prop} (before : BST 0 n)
    (key start : ℕ) (states : HeapSides n) (closed : HeapClosed family property states)
    (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (detachAll before key (conversionNames start) (conversionNames start) states) := by
  let selected := fun (owner : External n) (side : Bool) => growerHasKey key (states owner side)
  let converted := (convertHeap before.externalDepth selected start states).1
  have convertedClosed := convertHeap_closed family start property before.externalDepth selected states closed past
  apply heap_inherited convertedClosed hereditary (fun owner side => GrowthJournal.detachAll_grower before key start states owner side)
  intro owner side block member
  have equal : detachAll before key (conversionNames start) (conversionNames start) states owner side =
      eraseFrozenKey key (converted owner side) := by
    dsimp only [converted]
    rw [convertHeap_apply]
    rfl
  rw [equal] at member
  obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp member
  exact ⟨owner, side, old, oldMem, erase_descends old key⟩

theorem detachPorts_closed {n family : ℕ} {property : Frozen → Prop} (before : BST 0 n)
    (start : ℕ) (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (closed : HeapClosed family property states) (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => exact closed
  | cons key rest ih =>
      exact ih (stage+1) _ (detachAll_closed before key (start + Fintype.card (Place n)*stage) states closed hereditary
        (past.trans_le (Nat.le_add_right _ _)))

theorem preparation_closed {n family : ℕ} {property : Frozen → Prop} (before after : BST 0 n)
    (start : ℕ) (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n)
    (closed : HeapClosed family property states) (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (preparedForCuts before after start ports owners states) := by
  classical
  have grown := convertHeap_closed family start property before.externalDepth
    (fun owner side => decide (GrowerMismatch before after owner (states owner side))) states closed past
  rw [← prepareAllGrowers_fresh_eq] at grown
  have detached := detachPorts_closed before start ports 1 _ grown hereditary past
  have sealed := convertHeap_closed family (start + Fintype.card (Place n)*(ports.length+1)) property before.externalDepth
    (fun owner _ => decide (owner ∈ owners)) _ detached (past.trans_le (Nat.le_add_right _ _))
  rw [← sealOwners_fresh_eq] at sealed
  simpa only [preparedForCuts, sequenceNames, Nat.mul_zero, Nat.add_zero] using sealed

theorem allocated_preparation_closed {n family depth : ℕ} {property : Frozen → Prop} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (closed : HeapClosed family property states)
    (hereditary : Hereditary property) (past : family < start) :
    HeapClosed family property (allocateComparatorPreparation profile ports owners start states).states :=
  allocateCuts_closed profile.entries _ _ (preparation_closed before after start ports owners states closed hereditary past) hereditary

end Greedy.ClosedFamilies
