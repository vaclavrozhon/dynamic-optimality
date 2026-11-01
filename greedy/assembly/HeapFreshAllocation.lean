import FreshCutJournal
import InitialSnapshots
import OrderedUniversalComparator

/-!
The finite allocator is used on the literal owner/side table of the actual
heap. Its initial invariant is constructed from the actual canonical child
lists, with no initial freshness or coverage assumptions.
-/

namespace GreedyMerge.HeapAllocation

open OrderedBlocks FreshIds
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical

abbrev Place (n : ℕ) := External n × Bool
abbrev Slot (n : ℕ) := Fin (Fintype.card (Place n))

noncomputable def encode (n : ℕ) : Place n ≃ Slot n := Fintype.equivFin (Place n)

noncomputable def table {n : ℕ} (states : HeapSides n) : Slot n → SideState :=
  fun slot => states ((encode n).symm slot).1 ((encode n).symm slot).2

noncomputable def heap {n : ℕ} (states : Slot n → SideState) : HeapSides n :=
  fun owner side => states (encode n (owner, side))

@[simp] theorem heap_table {n : ℕ} (states : HeapSides n) : heap (table states) = states := by
  funext owner side
  simp [heap, table]

@[simp] theorem table_heap {n : ℕ} (states : Slot n → SideState) : table (heap states) = states := by
  funext slot
  simp [heap, table]

@[simp] theorem slot_count (n : ℕ) : Fintype.card (Place n) = 2 * (2*n+1) := by
  simp [Place, External, Nat.mul_comm]

noncomputable def sides (n : ℕ) (slot : Slot n) : Bool := ((encode n).symm slot).2

noncomputable def owners (n : ℕ) (slot : Slot n) : ℕ := ((encode n).symm slot).1.val

abbrev HeapInventory {n : ℕ} (states : HeapSides n) (next : ℕ) :=
  Inventory (table states) next

theorem initial_inventory {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    HeapInventory (InitialBlocks.state snapshot tree K) (2 * (2*n+1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro slot
    simp [table, InitialBlocks.state, liveIds]
  · intro first second id firstMember secondMember
    have firstEqual : id = InitialBlocks.slot ((encode n).symm first).1 ((encode n).symm first).2 := by
      simpa [table, InitialBlocks.state, liveIds] using firstMember
    have secondEqual : id = InitialBlocks.slot ((encode n).symm second).1 ((encode n).symm second).2 := by
      simpa [table, InitialBlocks.state, liveIds] using secondMember
    obtain ⟨ownerEqual, sideEqual⟩ := InitialBlocks.slot_injective _ _ _ _
      (firstEqual.symm.trans secondEqual)
    exact (encode n).symm.injective (Prod.ext ownerEqual sideEqual)
  · intro slot id member
    have equal : id = InitialBlocks.slot ((encode n).symm slot).1 ((encode n).symm slot).2 := by
      simpa [table, InitialBlocks.state, liveIds] using member
    rw [equal]
    exact List.mem_range.mp (InitialBlocks.slot_mem_birthIds _ _)

theorem initial_ready {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) :
    Ready comparator tree (InitialBlocks.state (Snapshot.ofTree comparator) tree K) := by
  refine ⟨InitialBlocks.state_valid _ _ _, InitialBlocks.state_sound _ _ _,
    InitialBlocks.state_complete _ _ _, InitialBlocks.state_persistent _ _ _, ?_⟩
  intro owner side block member
  simp [InitialBlocks.state] at member

noncomputable def cutHeap {n : ℕ} (cut start : ℕ) (states : HeapSides n) : HeapSides n × ℕ :=
  let output := freshCutStates (sides n) cut start (table states)
  (heap output.1, output.2)

noncomputable def cutNames {n : ℕ} (start : ℕ) (states : HeapSides n)
    (owner : External n) (side : Bool) : ℕ :=
  start + reserveWidth (fun slot => (table states slot).shrinking) * (encode n (owner, side)).val

theorem cutHeap_eq_cutAllOwners {n : ℕ} (cut start : ℕ) (states : HeapSides n) :
    (cutHeap cut start states).1 = cutAllOwners cut (cutNames start states) states := by
  funext owner side
  simp [cutHeap, freshCutStates, heap, table, sides, cutNames, cutAllOwners]

theorem cutHeap_inventory {n : ℕ} (cut start : ℕ) (states : HeapSides n)
    (inventory : HeapInventory states start) :
    HeapInventory (cutHeap cut start states).1 (cutHeap cut start states).2 := by
  simpa only [HeapInventory, cutHeap, table_heap] using
    freshCutStates_inventory (sides n) cut start (table states) inventory

noncomputable def convertHeap {n : ℕ} (rank : ℕ → ℕ)
    (selected : External n → Bool → Bool) (start : ℕ) (states : HeapSides n) : HeapSides n × ℕ :=
  let selectedSlots := fun slot : Slot n => selected ((encode n).symm slot).1 ((encode n).symm slot).2
  let output := freshConversions (owners n) (fun slot => rank (owners n slot)) selectedSlots start (table states)
  (heap output.1, output.2)

theorem convertHeap_apply {n : ℕ} (rank : ℕ → ℕ)
    (selected : External n → Bool → Bool) (start : ℕ) (states : HeapSides n)
    (owner : External n) (side : Bool) :
    (convertHeap rank selected start states).1 owner side =
      if selected owner side then
        convert owner.val (start + (encode n (owner, side)).val)
          (start + (encode n (owner, side)).val) (rank owner.val) (states owner side)
      else states owner side := by
  simp [convertHeap, heap, freshConversions, owners, table]

theorem convertHeap_inventory {n : ℕ} (rank : ℕ → ℕ)
    (selected : External n → Bool → Bool) (start : ℕ) (states : HeapSides n)
    (inventory : HeapInventory states start) :
    HeapInventory (convertHeap rank selected start states).1 (convertHeap rank selected start states).2 := by
  dsimp only [convertHeap]
  simp only [HeapInventory, table_heap]
  exact freshConversions_inventory _ _ _ start (table states) inventory

end GreedyMerge.HeapAllocation

#print axioms GreedyMerge.HeapAllocation.initial_inventory
#print axioms GreedyMerge.HeapAllocation.initial_ready
#print axioms GreedyMerge.HeapAllocation.cutHeap_inventory
