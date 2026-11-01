import BlockDepartures
import HarmfulBoundary
import SparseHarmfulGeometry

namespace GreedyForest.Execution

open scoped BigOperators

/-- A positive root-phase departure projects either to a below-floor
incoming edge of the active Cartesian tree on the block interval or to
one of two inactive separator endpoint exceptions. The active-edge count
is derived on an actual indexed BST by HarmfulBoundary.lean. -/
structure DenseHarmfulPhaseGeometry (count : ℕ) where
  lo : ℕ
  hi : ℕ
  first : ℕ
  finish : ℕ
  base : ℕ
  parentRank : ℕ
  rank : ℕ → ℕ
  tree : Splay.Tree.BST lo hi
  heap : GreedyMerge.HarmfulBoundary.Heap rank tree
  floor : ∀ key, lo ≤ key → key < hi → first ≤ key → key < finish → base ≤ rank key
  project : Fin count → Sum
    (Fin (GreedyMerge.HarmfulBoundary.EntryCount rank first finish base parentRank tree)) (Fin 2)
  injective : Function.Injective project

theorem DenseHarmfulPhaseGeometry.bound {count : ℕ} (h : DenseHarmfulPhaseGeometry count) :
    count ≤ 3 := by
  have hproj := Fintype.card_le_of_injective h.project h.injective
  have hc : count ≤
      GreedyMerge.HarmfulBoundary.EntryCount h.rank h.first h.finish h.base h.parentRank h.tree + 2 := by
    simpa using hproj
  have ht := GreedyMerge.HarmfulBoundary.entryCount_le_one h.rank h.tree h.heap h.floor
    (parentRank := h.parentRank)
  omega

/-- The actual retained records have holes where inactive values were
removed. This alternative keeps their literal sparse ordered heap. -/
structure SparseHarmfulPhaseGeometry (count : ℕ) where
  first : ℕ
  finish : ℕ
  base : ℕ
  parentRank : ℕ
  rank : ℕ → ℕ
  tree : ActiveTree.Sparse
  ordered : ActiveTree.Sparse.Ordered tree
  heap : ActiveTree.Sparse.Heap rank tree
  floor : ∀ key ∈ tree.keys, first ≤ key → key < finish → base ≤ rank key
  project : Fin count → Sum
    (Fin (ActiveTree.Sparse.belowEntries rank first finish base parentRank tree).card) (Fin 2)
  injective : Function.Injective project

theorem SparseHarmfulPhaseGeometry.bound {count : ℕ} (h : SparseHarmfulPhaseGeometry count) :
    count ≤ 3 := by
  have hproj := Fintype.card_le_of_injective h.project h.injective
  have hc : count ≤
      (ActiveTree.Sparse.belowEntries h.rank h.first h.finish h.base h.parentRank h.tree).card+2 := by
    simpa using hproj
  have ht := ActiveTree.Sparse.belowEntries_card_le_one h.rank h.first h.finish h.base
    h.tree h.ordered h.heap h.floor h.parentRank
  omega

inductive HarmfulPhaseGeometry (count : ℕ) where
  | dense : DenseHarmfulPhaseGeometry count → HarmfulPhaseGeometry count
  | sparse : SparseHarmfulPhaseGeometry count → HarmfulPhaseGeometry count

theorem HarmfulPhaseGeometry.bound {count : ℕ} (h : HarmfulPhaseGeometry count) :
    count ≤ 3 := by
  cases h with
  | dense hd => exact hd.bound
  | sparse hs => exact hs.bound

structure HarmfulEventLifetime (Record Event : Type*) [DecidableEq Record]
    (stages : ℕ) (events : Fin stages → Finset Event) (record : Event → Record)
    extends EventDepartureHistory Record Event stages events record where
  geometry : ∀ p, HarmfulPhaseGeometry (events p).card

theorem HarmfulEventLifetime.bound {Record Event : Type*} [DecidableEq Record]
    {stages : ℕ} {events : Fin stages → Finset Event} {record : Event → Record}
    (h : HarmfulEventLifetime Record Event stages events record) :
    (∑ p, (events p).card) ≤ 4 := by
  exact h.toEventDepartureHistory.bound (fun p => (h.geometry p).bound)

end GreedyForest.Execution
