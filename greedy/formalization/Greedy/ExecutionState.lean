import Greedy.AccessCost
import AccessInventory
import InitialSnapshots
import Greedy.FreshComparator
import Greedy.FreshRecanonicalization

/-!
# A concrete state for the shared Greedy/comparator execution

The surface and access time define geometric Greedy. The comparator,
canonical refinement, and ordered blocks are its accounting representation.
The separate entry clock and allocator counter retain immutable history
and globally distinct live instance names.
-/

namespace Greedy.Execution

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau

structure State (n : ℕ) where
  surface : Surface
  time : ℤ
  comparator : BST 0 n
  refined : Refinement surface comparator
  blocks : HeapSides n
  clock : ℕ
  next : ℕ

def State.Valid {n : ℕ} (state : State n) : Prop :=
  Ready state.comparator state.refined.tree state.blocks ∧
    Chronology state.clock state.blocks ∧ HeapInventory state.blocks state.next ∧
    ∀ key, key < n → state.surface key < state.time

noncomputable def initial {n : ℕ} (tree comparator : BST 0 n) (K : ℤ) : State n :=
  let height := initialSurface tree
  let refined := refinement height comparator
  ⟨height, 1, comparator, refined,
    GreedyMerge.InitialBlocks.state (Snapshot.ofTree comparator) refined.tree K,
    GreedyMerge.InitialBlocks.epoch n, 2*(2*n+1)⟩

theorem initial_valid {n : ℕ} (tree comparator : BST 0 n) (K : ℤ) : (initial tree comparator K).Valid := by
  refine ⟨initial_ready comparator _ K, ?_, initial_inventory _ _ K, ?_⟩
  · exact (chronology_iff ..).mpr
      ⟨GreedyMerge.InitialBlocks.state_histories _ _ _, GreedyMerge.InitialBlocks.state_beforeTime _ _ _⟩
  · intro key _
    exact initialSurface_lt_one tree key

/-- One epoch is reserved for administrative label changes before the
first paid entry. Subsequent entries read their literal pre-insertion state. -/
noncomputable def entryReader {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (clock stage : ℕ) (current : HeapSides n) (record owner : External n) : Entry :=
  let label := GreedyMerge.StateLabels.label comparator.externalDepth K current
  ⟨record.val, clock+1+stage, label record.val, label owner.val⟩

theorem root_minimum {n : ℕ} (tree : BST 0 n) (request : Fin n) (root : tree.HasRoot request.val) :
    GreedyMerge.Surface.UniqueGlobalMinimum tree.depth n request.val := by
  obtain ⟨left, right, rfl⟩ := root
  refine ⟨request.isLt, ?_⟩
  intro key _ different
  rw [depth_root]
  by_cases less : key < request.val
  · rw [depth_node_of_lt_root left right less]
    omega
  · rw [depth_node_of_root_lt left right (by omega)]
    omega

theorem raised_fresh {n : ℕ} (surface : Surface) (time : ℤ) (request : Fin n)
    (fresh : ∀ key, key < n → surface key < time) :
    ∀ key, key < n → GreedyMerge.Surface.RaiseSurface surface n request.val time key < time + 1 := by
  intro key inside
  have old := fresh key inside
  unfold GreedyMerge.Surface.RaiseSurface
  split_ifs <;> omega

def source {n : ℕ} (request : Fin n) : External n := ⟨2*request.val+1, by have := request.isLt; omega⟩

noncomputable def afterRefinement {n : ℕ} (state : State n) (request : Fin n) :
    Refinement (GreedyMerge.Surface.RaiseSurface state.surface n request.val state.time) state.comparator :=
  refinement _ _

noncomputable def afterAccess {n : ℕ} (state : State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition state.refined.tree request.val)
    (data : AccessScheduleData state.comparator state.refined.tree (afterRefinement state request).tree decomposition) :
    State n :=
  let prepared := (convertHeap state.comparator.externalDepth
    (fun owner _ => decide (owner = source request)) state.next state.blocks).1
  let reader := fun (_ : ℕ) (current : HeapSides n) =>
    GreedyMerge.StateLabels.label state.comparator.externalDepth K current
  let side := fun event : External n × External n => decide (event.2.val < (source request).val)
  ⟨GreedyMerge.Surface.RaiseSurface state.surface n request.val state.time, state.time+1,
    state.comparator, afterRefinement state request,
    runLinks (source request) side reader state.clock prepared data.events,
    state.clock+data.events.length, state.next+2*(2*n+1)⟩

theorem access_exists {n : ℕ} (state : State n) (request : Fin n) (K : ℤ)
    (valid : state.Valid) (root : state.comparator.HasRoot request.val) :
    ∃ decomposition : Decomposition state.refined.tree request.val,
      ∃ data : AccessScheduleData state.comparator state.refined.tree (afterRefinement state request).tree decomposition,
        (afterAccess state request K decomposition data).Valid ∧
        data.events.length = 2*((GreedyMerge.Geometry.GreedyRow state.surface n request.val).card - 1) := by
  obtain ⟨decomposition⟩ := exists_decomposition state.refined.tree request.isLt
  let next := afterRefinement state request
  obtain ⟨histories, beforeClock⟩ := (chronology_iff ..).mp valid.2.1
  obtain ⟨data, ready, history, clock, inventory, _labels, _degree, _births⟩ :=
    actual_access_allocated state.surface state.time state.comparator state.refined.tree next.tree
      state.refined.owner next.owner state.refined.owners next.owners (root_minimum _ request root)
      valid.2.2.2 state.refined.canonical next.canonical decomposition (source request) rfl
      state.blocks K state.clock state.next valid.1 histories beforeClock valid.2.2.1
  refine ⟨decomposition, data, ⟨ready, (chronology_iff ..).mpr ⟨history, clock⟩, inventory,
    raised_fresh state.surface state.time request valid.2.2.2⟩, ?_⟩
  exact actual_access_link_count state.surface state.comparator state.refined.tree next.tree
    state.refined.owner state.refined.owners (root_minimum _ request root) state.refined.canonical decomposition data

end Greedy.Execution
