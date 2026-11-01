import Greedy.AccessMemoryRun
import Greedy.AccessPhaseSum
import Greedy.AccessMeasurements

/-! Latest creator memories are preserved by an actual geometric access. -/

namespace Greedy.LiveMemory

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation EntryJournal RestorationJournal
open GreedyMerge.AccessSourceAccounting GreedyMerge.PathPlateau

theorem access {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (root : before.comparator.HasRoot request.val)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator K before.blocks)
    (synced : Synced state.memory before.blocks) :
    Synced (run state (RunJournal.access before request decomposition data)).memory
      (Execution.afterAccess before request K decomposition data).blocks := by
  let source := Execution.source request
  let selected := fun (owner : External n) (_ : Bool) => decide (owner = source)
  let prepared := RunJournal.prepared before request
  have memory : Synced state.memory prepared :=
    EntryProperties.convertHeap_property before.comparator.externalDepth selected before.next before.blocks synced
  have ready := CreatorPhase.prepared_ready before request valid
  have geometry := AccessTrace.geometry data source rfl (Execution.root_minimum _ request root)
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth source before.next before.blocks
  change convertRoot before.comparator.externalDepth source (rootNames source before.next)
    (rootNames source before.next) before.blocks = prepared at converted
  have empty : ∀ side, growerEntries (prepared source side).grower = [] := by
    intro side
    rw [← converted]
    exact convertRoot_empty _ _ _ _ _ side
  let sideOf := fun event : External n × External n => decide (event.2.val < source.val)
  apply runLinks_memory (canonicalParent (Snapshot.ofTree before.comparator) before.refined.tree)
    before.comparator.externalDepth K source sideOf before.clock prepared data.events
    (AccessTrace.roots data) (AccessTrace.survivors data) geometry.run geometry.unique
  · intro record member
    exact hasChild_parent _ _ source record ((geometry.children _).mpr member)
  · intro record member
    exact hasChild_ne_owner _ _ source record ((geometry.children _).mpr member)
  · exact ready.sound
  · intro record owner parent
    exact ready.complete record owner parent (by simp)
  · exact ready.persistent
  · exact empty
  · intros; rfl
  · exact orderedPrefixes_of_canonical (Snapshot.ofTree before.comparator) before.refined.tree source sideOf prepared
      ready.sound ready.valid ready.persistent empty before.comparator.externalDepth data.events
      (AccessTrace.roots data) (AccessTrace.survivors data) geometry.run geometry.children _ before.clock geometry.arrivals
  · intro record
    rw [agree, ← RunJournal.prepared_labels before request K]
    rfl
  · exact memory

end Greedy.LiveMemory
