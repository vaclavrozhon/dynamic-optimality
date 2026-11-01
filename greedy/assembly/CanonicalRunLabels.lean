import ActualRunLabels
import ComparatorHeapEdges

/-!
Discharge the structural prefix conditions of ActualRunLabels from the
actual old canonical heap and literal schedule arrival order. This gives
the exact Phase.labelsAt function at every executed prefix, including
the two immutable labels captured before a loser update.
-/
namespace GreedyMerge.ActualLinks

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open OrderedBlocks Primitives GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge.AccessFrontier

theorem hasChild_parent {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (owner child : External n)
    (member : HasChild snapshot tree (Nat.le_refl n) 0 owner child.val) :
    canonicalParent snapshot tree child=some owner := by
  obtain ⟨edge,edgeMem,ownerEq,childEq⟩ := member
  have same : edge.child=child := Fin.ext childEq
  simpa only [same,ownerEq] using ComparatorHeap.parent_of_fullEdge snapshot tree edge edgeMem

theorem orderedPrefixes_of_canonical {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (source : External n) (sourceSide : External n × External n → Bool) (states : States n)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (rank : ℕ → ℕ) (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (links : Run rank (events.map eventKeys) roots finalRoots)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child∈roots)
    (reader : ℕ → States n → ℕ → ℤ) (time : ℕ)
    (arrivalOrders : ∀ event∈events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event))) :
    ∀ first second, events=first++second → Ordered (runLinks source sourceSide reader time states first) := by
  intro first second split
  have lengthBound : first.length≤(events.map eventKeys).length := by simp [split]
  obtain ⟨middle,firstRun,_⟩ := GreedyForest.Phase.run_take_split links first.length lengthBound
  have mappedTake : (events.map eventKeys).take first.length=first.map eventKeys := by simp [split]
  rw [mappedTake] at firstRun
  apply runLinks_ordered snapshot tree source sourceSide states sound ordered persistent emptySource
    rank first roots middle firstRun actualChildren reader time
  intro event member
  have full := arrivalOrders event (by rw [split]; exact List.mem_append_left _ member)
  rw [split,List.map_append,arrivals_append] at full
  exact (List.pairwise_append.mp full).1

theorem runLinks_canonical_sound_complete_labels {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n) (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (reader : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (links : Run rank (events.map eventKeys) roots finalRoots) (uniqueRoots : roots.Nodup)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child∈roots)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (complete : CompleteFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (sideCorrect : ∀ event∈events, sourceSide event=decide (event.2.val<source.val))
    (arrivalOrders : ∀ event∈events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event))) :
    SoundFor (runParents (canonicalParent snapshot tree) events)
      (runLinks source sourceSide reader time states events) ∧
    CompleteFor (runParents (canonicalParent snapshot tree) events)
      (runLinks source sourceSide reader time states events) ∧
    StateLabels.label rank K (runLinks source sourceSide reader time states events) =
      GreedyForest.Phase.runLabels rank (StateLabels.label rank K states) (events.map eventKeys) := by
  apply runLinks_sound_complete_labels (canonicalParent snapshot tree) rank K source sourceSide
    reader time states events roots finalRoots links uniqueRoots
  · intro record member
    exact hasChild_parent snapshot tree source record ((actualChildren _).mpr member)
  · intro record member
    exact hasChild_ne_owner snapshot tree source record ((actualChildren _).mpr member)
  · exact sound
  · exact complete
  · exact persistent
  · exact emptySource
  · exact sideCorrect
  · exact orderedPrefixes_of_canonical snapshot tree source sourceSide states sound ordered
      persistent emptySource rank events roots finalRoots links actualChildren reader time arrivalOrders

/-- Every actual prefix state reads exactly the accounting prefix labels.
The comparison holds on all natural keys, including absent root records
with the unchanged fallback K. -/
theorem runLinks_labelsAt {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n) (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (reader : ℕ → States n → ℕ → ℤ) (time : ℕ) (states : States n)
    (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (links : Run rank (events.map eventKeys) roots finalRoots) (uniqueRoots : roots.Nodup)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child∈roots)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (complete : CompleteFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (sideCorrect : ∀ event∈events, sourceSide event=decide (event.2.val<source.val))
    (arrivalOrders : ∀ event∈events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event)))
    (count : ℕ) (prefixBound : count≤events.length) :
    StateLabels.label rank K (runLinks source sourceSide reader time states (events.take count)) =
      GreedyForest.Phase.labelsAt rank (StateLabels.label rank K states) (events.map eventKeys) count := by
  obtain ⟨middle,prefixLinks,_⟩ := GreedyForest.Phase.run_take_split links count
    (by simpa only [List.length_map] using prefixBound)
  rw [←List.map_take] at prefixLinks
  have prefixArrival : ∀ event∈events.take count,
      (arrivals (targetSide event) event.1.val ((events.take count).map eventKeys)).Pairwise
        (arrivalOrder (targetSide event)) := by
    intro event member
    have full := arrivalOrders event (List.mem_of_mem_take member)
    have split : events=events.take count++events.drop count := (List.take_append_drop count events).symm
    rw [split,List.map_append,arrivals_append] at full
    exact (List.pairwise_append.mp full).1
  have result := runLinks_canonical_sound_complete_labels snapshot tree rank K source sourceSide reader
    time states (events.take count) roots middle prefixLinks uniqueRoots actualChildren sound complete
    ordered persistent emptySource (fun event member => sideCorrect event (List.mem_of_mem_take member)) prefixArrival
  simpa only [GreedyForest.Phase.labelsAt,List.map_take] using result.2.2


/-- The literal arrival record created by the indexed executed step. -/
noncomputable def indexedArrival {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (time : ℕ) (states : States n) (events : List (External n × External n))
    (event : Fin events.length) : Entry :=
  let current := runLinks source sourceSide (fun _ current => StateLabels.label rank K current)
    time states (events.take event.val)
  arrivalEntry (StateLabels.label rank K current) (events.get event).1 (events.get event).2 (time+event.val)

theorem indexedArrival_step {n : ℕ} (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (time : ℕ) (states : States n) (events : List (External n × External n))
    (event : Fin events.length) :
    runLinks source sourceSide (fun _ current => StateLabels.label rank K current)
      time states (events.take (event.val+1)) =
    linkState (runLinks source sourceSide (fun _ current => StateLabels.label rank K current)
      time states (events.take event.val)) source (events.get event).1 (events.get event).2
      (sourceSide (events.get event)) (targetSide (events.get event))
      (indexedArrival rank K source sourceSide time states events event) := by
  rw [List.take_succ_eq_append_getElem event.isLt,runLinks_append]
  simp only [runLinks,List.length_take,Nat.min_eq_left (Nat.le_of_lt event.isLt),indexedArrival]
  rfl

/-- Both immutable entry labels are the genuine pre-loser-update phase
snapshots; the timestamp is the exact global phase offset plus index. -/
theorem indexedArrival_snapshots {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n) (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (time : ℕ) (states : States n) (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (links : Run rank (events.map eventKeys) roots finalRoots) (uniqueRoots : roots.Nodup)
    (actualChildren : ∀ child, HasChild snapshot tree (Nat.le_refl n) 0 source child ↔ child∈roots)
    (sound : SoundFor (canonicalParent snapshot tree) states)
    (complete : CompleteFor (canonicalParent snapshot tree) states)
    (ordered : Ordered states) (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (sideCorrect : ∀ event∈events, sourceSide event=decide (event.2.val<source.val))
    (arrivalOrders : ∀ event∈events,
      (arrivals (targetSide event) event.1.val (events.map eventKeys)).Pairwise
        (arrivalOrder (targetSide event))) (event : Fin events.length) :
    let fresh := indexedArrival rank K source sourceSide time states events event
    fresh.key=(events.get event).2.val ∧ fresh.joined=time+event.val ∧
    fresh.entryLabel=GreedyForest.Phase.labelsAt rank (StateLabels.label rank K states)
      (events.map eventKeys) event.val (events.get event).2.val ∧
    fresh.creatorLabel=GreedyForest.Phase.labelsAt rank (StateLabels.label rank K states)
      (events.map eventKeys) event.val (events.get event).1.val := by
  have labels := runLinks_labelsAt snapshot tree rank K source sourceSide
    (fun _ current => StateLabels.label rank K current) time states events roots finalRoots links uniqueRoots
    actualChildren sound complete ordered persistent emptySource sideCorrect arrivalOrders
    event.val (Nat.le_of_lt event.isLt)
  simp only [indexedArrival,arrivalEntry,labels,and_self]

end GreedyMerge.ActualLinks

#print axioms GreedyMerge.ActualLinks.runLinks_canonical_sound_complete_labels
#print axioms GreedyMerge.ActualLinks.runLinks_labelsAt

#print axioms GreedyMerge.ActualLinks.indexedArrival_step
#print axioms GreedyMerge.ActualLinks.indexedArrival_snapshots
