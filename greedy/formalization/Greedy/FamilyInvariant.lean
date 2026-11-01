import Greedy.FamilyOrderCuts
import Greedy.FamilyOrderTransfer
import Greedy.FamilyOrderPaid
import Greedy.FamilyRestoration

/-! Joint spatial-name and historical-order invariant for actual block states. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation GreedyMerge.ActualLinks

structure Invariant {n : ℕ} (clock next : ℕ) (states : HeapSides n) : Prop where
  names : FamilyNames.HeapFamilyInventory states next
  ordered : HeapOrdered states
  chronology : Chronology clock states
  ids : HeapInventory states next

theorem Invariant.advance {n clock next : ℕ} {states : HeapSides n} (inv : Invariant clock next states)
    (later : ℕ) (bound : clock ≤ later) : Invariant later next states :=
  ⟨inv.names, inv.ordered, inv.chronology.mono bound, inv.ids⟩

theorem initial_invariant {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n) (K : ℤ) :
    Invariant (GreedyMerge.InitialBlocks.epoch n) (2*(2*n+1)) (GreedyMerge.InitialBlocks.state snapshot tree K) :=
  ⟨FamilyNames.initial_inventory snapshot tree K, initial_ordered snapshot tree K,
    (chronology_iff ..).mpr ⟨GreedyMerge.InitialBlocks.state_histories _ _ _, GreedyMerge.InitialBlocks.state_beforeTime _ _ _⟩,
    GreedyMerge.HeapAllocation.initial_inventory snapshot tree K⟩

theorem convertHeap_invariant {n clock : ℕ} (rank : ℕ → ℕ) (selected : External n → Bool → Bool)
    (start : ℕ) (states : HeapSides n) (inv : Invariant clock start states) :
    Invariant clock (start + Fintype.card (Place n)) (convertHeap rank selected start states).1 := by
  refine ⟨FamilyNames.convertHeap_inventory rank selected start states inv.names,
    convertHeap_ordered rank selected start states inv.ordered inv.names ((chronology_iff ..).mp inv.chronology).1,
    ?_, GreedyMerge.HeapAllocation.convertHeap_inventory rank selected start states inv.ids⟩
  intro owner side
  rw [convertHeap_apply]
  split_ifs
  · exact conversion_chronology _ _ _ _ clock _ (inv.chronology owner side)
  · exact inv.chronology owner side

theorem allocated_preparation_invariant {n clock depth : ℕ} {before after : BST 0 n}
    (profile : RotationCutProfile before after depth) (start : ℕ) (ports : List ℕ)
    (owners : Finset (External n)) (states : HeapSides n) (inv : Invariant clock start states) :
    Invariant clock (allocateComparatorPreparation profile ports owners start states).next
      (allocateComparatorPreparation profile ports owners start states).states := by
  refine ⟨FamilyNames.allocated_preparation_inventory profile start ports owners states inv.names,
    allocated_preparation_ordered profile start ports owners states inv.ordered inv.names inv.chronology,
    ?_, allocateComparatorPreparation_inventory profile ports owners start states inv.ids⟩
  rw [← allocateComparatorPreparation_eq]
  exact prepareComparator_chronology profile _ _ ports owners clock states inv.chronology

theorem detachPorts_invariant {n clock : ℕ} (before : BST 0 n) (start : ℕ) (ports : List ℕ)
    (stage : ℕ) (states : HeapSides n) (inv : Invariant clock (start + Fintype.card (Place n)*stage) states) :
    Invariant clock (start + Fintype.card (Place n)*(stage+ports.length))
      (detachPorts before (sequenceNames start) (sequenceNames start) ports stage states).1 :=
  ⟨FamilyNames.detachPorts_inventory before start ports stage states inv.names,
    detachPorts_ordered before start ports stage states inv.ordered inv.names inv.chronology,
    detachPorts_chronology before _ _ ports stage clock states inv.chronology,
    detachPorts_fresh_inventory before start ports stage states inv.ids⟩

theorem rebase_invariant {n clock next : ℕ} (before after : BST 0 n) (states : HeapSides n)
    (inv : Invariant clock next states) : Invariant clock next (rebaseAll before after states) :=
  ⟨FamilyNames.rebase_inventory before after states inv.names, rebase_ordered before after states inv.ordered inv.ids,
    rebaseAll_chronology before after clock states inv.chronology, rebaseAll_inventory before after states next inv.ids⟩

theorem junction_invariant {n clock : ℕ} (oldOwner newOwner : External n) (different : oldOwner ≠ newOwner)
    (lo hi start : ℕ) (states : HeapSides n) (inv : Invariant clock start states) :
    Invariant clock (allocateJunction oldOwner newOwner lo hi start states).next
      (allocateJunction oldOwner newOwner lo hi start states).states := by
  refine ⟨FamilyNames.junction_inventory oldOwner newOwner lo hi start states inv.names,
    junction_ordered oldOwner newOwner different lo hi start states inv.ordered inv.ids, ?_,
    allocateJunction_inventory oldOwner newOwner different lo hi start states inv.ids⟩
  rw [allocateJunction_eq]
  exact moveJunction_chronology oldOwner newOwner lo hi _ clock states inv.chronology

theorem restorePort_ordered {n clock start : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (states : HeapSides n) (inv : Invariant clock start states) :
    HeapOrdered (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1 := by
  cases parent : canonicalParent snapshot tree record with
  | none => simpa only [restorePort, parent] using inv.ordered
  | some owner =>
      let side := decide (record.val < owner.val)
      let slot := encode n (owner, side)
      have supplied := freshPaidSlot_ordered slot owner.val (snapshot.rank owner) side (makeEntry owner) (table states)
        inv.ordered inv.names (fun slot grower present => (((chronology_iff ..).mp inv.chronology).1 _ _).2 grower present)
      have receiver : table states slot = states owner side := by simp [table, slot]
      have mapped : HeapOrdered
          (heap (GreedyMerge.FreshIds.freshPaidSlot slot owner.val (snapshot.rank owner) side start (makeEntry owner) (table states)).1) := by
        simpa only [HeapOrdered, table_heap] using supplied
      dsimp only [GreedyMerge.FreshIds.freshPaidSlot] at mapped
      rw [receiver, heap_update] at mapped
      simpa only [restorePort, portNames, parent, GreedyMerge.FreshIds.freshPaidInsertion] using mapped

theorem restorePort_invariant {n clock start : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (record : External n) (makeEntry : External n → Entry) (time : ∀ owner, (makeEntry owner).joined = clock)
    (states : HeapSides n) (inv : Invariant clock start states) :
    Invariant (clock+1) (restoreNext snapshot tree record start states)
      (restorePort snapshot tree (portNames snapshot tree record start states) makeEntry record states).1 :=
  ⟨FamilyNames.restorePort_inventory snapshot tree record makeEntry start states inv.names,
    restorePort_ordered snapshot tree record makeEntry states inv,
    restorePort_chronology snapshot tree _ makeEntry record clock states inv.chronology time,
    restorePort_fresh_inventory snapshot tree record makeEntry start states inv.ids⟩

end Greedy.FamilyOrder
