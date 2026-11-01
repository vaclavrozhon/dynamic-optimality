import Greedy.FamilyOrderConversions
import Greedy.FamilyPreparation

/-! Historical interval order survives actual cuts and port detachment. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks

theorem cutAllOwners_ordered {n : ℕ} (cut : ℕ) (names : External n → Bool → ℕ)
    (states : HeapSides n) (ordered : HeapOrdered states) : HeapOrdered (cutAllOwners cut names states) :=
  cut_ordered (fun slot => ((encode n).symm slot).2) cut
    (fun slot => names ((encode n).symm slot).1 ((encode n).symm slot).2) (table states) ordered

theorem prepareCuts_ordered {n : ℕ} (names : NameSupply n) (cuts : List (ℕ × ℕ))
    (stage : ℕ) (states : HeapSides n) (ordered : HeapOrdered states) :
    HeapOrdered (prepareCuts names cuts stage states).1 := by
  induction cuts generalizing stage states with
  | nil => exact ordered
  | cons cut rest ih => exact ih (stage+1) _ (cutAllOwners_ordered cut.1 (names stage) states ordered)

theorem allocateCuts_ordered {n : ℕ} (cuts : List (ℕ × ℕ)) (start : ℕ)
    (states : HeapSides n) (ordered : HeapOrdered states) : HeapOrdered (allocateCuts cuts start states).states := by
  have equal := congrArg Prod.fst (allocateCuts_eq cuts start states)
  dsimp only at equal
  rw [← equal]
  exact prepareCuts_ordered _ cuts 0 states ordered

theorem detachAll_ordered {n start : ℕ} (before : BST 0 n) (key : ℕ) (states : HeapSides n)
    (ordered : HeapOrdered states) (names : FamilyNames.HeapFamilyInventory states start) (histories : Histories states) :
    HeapOrdered (detachAll before key (conversionNames start) (conversionNames start) states) := by
  let selected := fun (owner : External n) (side : Bool) => growerHasKey key (states owner side)
  let converted := (convertHeap before.externalDepth selected start states).1
  have convertedOrder := convertHeap_ordered before.externalDepth selected start states ordered names histories
  have equal : detachAll before key (conversionNames start) (conversionNames start) states =
      fun owner side => eraseFrozenKey key (converted owner side) := by
    funext owner side
    dsimp only [converted]
    rw [convertHeap_apply]
    rfl
  rw [equal]
  exact erase_ordered (fun _ => key) (table converted) convertedOrder

theorem detachPorts_ordered {n clock : ℕ} (before : BST 0 n) (start : ℕ) (ports : List ℕ)
    (stage : ℕ) (states : HeapSides n) (ordered : HeapOrdered states)
    (names : FamilyNames.HeapFamilyInventory states (start + Fintype.card (Place n)*stage))
    (chronology : Chronology clock states) :
    HeapOrdered (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1 := by
  induction ports generalizing stage states with
  | nil => exact ordered
  | cons key rest ih =>
      have head := detachAll_ordered before key states ordered names ((chronology_iff ..).mp chronology).1
      have fresh := FamilyNames.detachAll_inventory before key (start + Fintype.card (Place n)*stage) states names
      have temporal := detachAll_chronology before key (sequenceNames start stage) (sequenceNames start stage) clock states chronology
      apply ih (stage+1) _ head _ temporal
      simpa only [sequenceNames, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using fresh

theorem preparation_ordered {n clock : ℕ} (before after : BST 0 n) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (ordered : HeapOrdered states)
    (names : FamilyNames.HeapFamilyInventory states start) (chronology : Chronology clock states) :
    HeapOrdered (preparedForCuts before after start ports owners states) := by
  classical
  let supply := sequenceNames (n:=n) start
  let growing := prepareAllGrowers before after (supply 0) (supply 0) states
  let detached := (detachPorts before supply supply ports 1 growing).1
  let selected := fun (owner : External n) (side : Bool) => decide (GrowerMismatch before after owner (states owner side))
  have growOrder := convertHeap_ordered before.externalDepth selected start states ordered names ((chronology_iff ..).mp chronology).1
  have growNames := FamilyNames.convertHeap_inventory before.externalDepth selected start states names
  rw [← prepareAllGrowers_fresh_eq] at growOrder growNames
  have growTime : Chronology clock growing := prepareAllGrowers_chronology before after _ _ clock states chronology
  have detachedOrder := detachPorts_ordered before start ports 1 growing
    (by simpa only [growing, supply, sequenceNames, Nat.mul_zero, Nat.add_zero] using growOrder)
    (by simpa only [growing, supply, sequenceNames, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using growNames) growTime
  have detachedNames := FamilyNames.detachPorts_inventory before start ports 1 growing
    (by simpa only [growing, supply, sequenceNames, Nat.mul_zero, Nat.add_zero, Nat.mul_one] using growNames)
  have detachedTime := detachPorts_chronology before supply supply ports 1 clock growing growTime
  have sealed := convertHeap_ordered before.externalDepth (fun owner _ => decide (owner ∈ owners))
    (start + Fintype.card (Place n)*(ports.length+1)) detached detachedOrder detachedNames ((chronology_iff ..).mp detachedTime).1
  rw [← sealOwners_fresh_eq] at sealed
  exact sealed

theorem allocated_preparation_ordered {n clock depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (ordered : HeapOrdered states)
    (names : FamilyNames.HeapFamilyInventory states start) (chronology : Chronology clock states) :
    HeapOrdered (allocateComparatorPreparation profile ports owners start states).states :=
  allocateCuts_ordered profile.entries _ _ (preparation_ordered before after start ports owners states ordered names chronology)

end Greedy.FamilyOrder
