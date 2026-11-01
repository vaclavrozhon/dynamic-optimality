import HeapFreshAllocation

/-!
Fresh names for the actual conversion/detachment/sealing prefix of a
comparator update. Each conversion stage reserves one name per owner/side;
the pre-existing exact birth journals charge only conversions that occur.
The same name is the newly born family's and replacement grower's id.
-/
namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

noncomputable def conversionNames {n : ℕ} (start : ℕ) (owner : External n) (side : Bool) : ℕ :=
  start + (encode n (owner,side)).val

noncomputable def sequenceNames {n : ℕ} (start : ℕ) : NameSupply n :=
  fun stage => conversionNames (start + Fintype.card (Place n)*stage)

theorem convertHeap_next {n : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) :
    (convertHeap rank selected start states).2 = start + Fintype.card (Place n) := rfl

theorem heapInventory_of_liveIds_eq {n : ℕ} (before after : HeapSides n) (next : ℕ)
    (same : ∀ owner side, liveIds (after owner side)=liveIds (before owner side))
    (inventory : HeapInventory before next) : HeapInventory after next := by
  have sameTable : ∀ slot, liveIds (table after slot)=liveIds (table before slot) := by
    intro slot
    exact same _ _
  refine ⟨?_,?_,?_⟩
  · intro slot
    rw [sameTable]
    exact inventory.localUnique slot
  · intro first second id firstMem secondMem
    rw [sameTable] at firstMem secondMem
    exact inventory.locations first second id firstMem secondMem
  · intro slot id member
    rw [sameTable] at member
    exact inventory.below slot id member

theorem prepareAllGrowers_fresh_eq {n : ℕ} (before after : BST 0 n) (start : ℕ) (states : HeapSides n) :
    prepareAllGrowers before after (conversionNames start) (conversionNames start) states =
      (convertHeap before.externalDepth (fun owner side => decide (GrowerMismatch before after owner (states owner side)))
        start states).1 := by
  funext owner side
  rw [convertHeap_apply]
  by_cases selected : GrowerMismatch before after owner (states owner side)
  · simp [prepareAllGrowers,prepareGrower,selected,conversionNames]
  · simp [prepareAllGrowers,prepareGrower,selected]

theorem prepareAllGrowers_fresh_inventory {n : ℕ} (before after : BST 0 n) (start : ℕ)
    (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (prepareAllGrowers before after (conversionNames start) (conversionNames start) states)
      (start+Fintype.card (Place n)) := by
  rw [prepareAllGrowers_fresh_eq]
  exact convertHeap_inventory before.externalDepth _ start states inventory

theorem detachAll_fresh_liveIds {n : ℕ} (before : BST 0 n) (key start : ℕ) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    liveIds (detachAll before key (conversionNames start) (conversionNames start) states owner side) =
      liveIds ((convertHeap before.externalDepth (fun owner side => growerHasKey key (states owner side)) start states).1 owner side) := by
  rw [convertHeap_apply]
  change liveIds (eraseFrozenKey key (sealPortSource owner.val (conversionNames start owner side)
    (conversionNames start owner side) (before.externalDepth owner.val) key (states owner side))) = _
  rw [eraseFrozenKey_id_support]
  rfl

theorem detachAll_fresh_inventory {n : ℕ} (before : BST 0 n) (key start : ℕ)
    (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (detachAll before key (conversionNames start) (conversionNames start) states)
      (start+Fintype.card (Place n)) := by
  exact heapInventory_of_liveIds_eq _ _ _ (detachAll_fresh_liveIds before key start states)
    (convertHeap_inventory before.externalDepth _ start states inventory)

theorem detachPorts_fresh_inventory {n : ℕ} (before : BST 0 n) (start : ℕ)
    (ports : List ℕ) (stage : ℕ) (states : HeapSides n)
    (inventory : HeapInventory states (start+Fintype.card (Place n)*stage)) :
    HeapInventory (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1
      (start+Fintype.card (Place n)*(stage+ports.length)) := by
  induction ports generalizing stage states with
  | nil => simpa only [List.length_nil,Nat.add_zero,detachPorts] using inventory
  | cons key rest ih =>
      have head := detachAll_fresh_inventory before key (start+Fintype.card (Place n)*stage) states inventory
      have head' : HeapInventory
          (detachAll before key (sequenceNames start stage) (sequenceNames start stage) states)
          (start+Fintype.card (Place n)*(stage+1)) := by
        simpa only [sequenceNames,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using head
      have tail := ih (stage+1) _ head'
      simpa only [detachPorts,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

theorem sealOwners_fresh_eq {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (start : ℕ) (states : HeapSides n) :
    sealOwners before owners (conversionNames start) (conversionNames start) states =
      (convertHeap before.externalDepth (fun owner _ => decide (owner ∈ owners)) start states).1 := by
  classical
  funext owner side
  rw [convertHeap_apply]
  by_cases selected : owner ∈ owners <;> simp [sealOwners,selected,conversionNames]

theorem sealOwners_fresh_inventory {n : ℕ} (before : BST 0 n) (owners : Finset (External n))
    (start : ℕ) (states : HeapSides n) (inventory : HeapInventory states start) :
    HeapInventory (sealOwners before owners (conversionNames start) (conversionNames start) states)
      (start+Fintype.card (Place n)) := by
  rw [sealOwners_fresh_eq]
  exact convertHeap_inventory before.externalDepth _ start states inventory

noncomputable def preparedForCuts {n : ℕ} (before after : BST 0 n) (start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n) : HeapSides n :=
  let names := sequenceNames start
  let growing := prepareAllGrowers before after (names 0) (names 0) states
  let detached := (detachPorts before names names ports 1 growing).1
  sealOwners before owners (names (ports.length+1)) (names (ports.length+1)) detached

theorem preparedForCuts_inventory {n : ℕ} (before after : BST 0 n) (start : ℕ)
    (ports : List ℕ) (owners : Finset (External n)) (states : HeapSides n)
    (inventory : HeapInventory states start) :
    HeapInventory (preparedForCuts before after start ports owners states)
      (start+Fintype.card (Place n)*(ports.length+2)) := by
  let names := sequenceNames (n:=n) start
  let growing := prepareAllGrowers before after (names 0) (names 0) states
  let detached := (detachPorts before names names ports 1 growing).1
  have grown : HeapInventory growing (start+Fintype.card (Place n)*1) := by
    simpa only [growing,names,sequenceNames,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
      prepareAllGrowers_fresh_inventory before after start states inventory
  have detachedInventory := detachPorts_fresh_inventory before start ports 1 growing grown
  have sealed := sealOwners_fresh_inventory before owners (start+Fintype.card (Place n)*(ports.length+1)) detached
    (by simpa only [Nat.add_comm] using detachedInventory)
  change HeapInventory (sealOwners before owners (names (ports.length+1)) (names (ports.length+1)) detached) _
  simpa only [names,sequenceNames,Nat.mul_add,Nat.mul_one,Nat.mul_two,Nat.add_assoc] using sealed

#print axioms prepareAllGrowers_fresh_inventory
#print axioms detachPorts_fresh_inventory
#print axioms preparedForCuts_inventory

end GreedyMerge.HeapAllocation
