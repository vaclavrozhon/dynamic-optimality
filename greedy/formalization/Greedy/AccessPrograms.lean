import Greedy.AccessVariation
import Greedy.RunJournal
import Greedy.RunLabelHistory

/-! The literal access history shares its journal and exact variation. -/

namespace Greedy.AccessPrograms

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open GreedyMerge.HeapAllocation EntryJournal RestorationJournal

theorem access_joint {n : ℕ} (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (root : before.comparator.HasRoot request.val)
    (creators : GrowthJournal.Creators before.blocks)
    (state : WeightedMemory.State (External n)) (old : LabelHistory.History (External n))
    (agree : state.label = labels before.comparator K before.blocks)
    (sound : LabelSnapshots.Sound before.comparator K before.clock before.blocks old) :
    ∃ history : LabelHistory.History (External n),
      LabelSnapshots.Sound before.comparator K (Greedy.Execution.afterAccess before request K decomposition data).clock
        (Greedy.Execution.afterAccess before request K decomposition data).blocks history ∧
      LabelHistory.Future old history before.clock ∧
      LabelHistory.variation history = LabelHistory.variation old +
        total absoluteChange state (RunJournal.access before request decomposition data) := by
  let source := Greedy.Execution.source request
  let selected := fun (owner : External n) (_ : Bool) => decide (owner = source)
  let prepared := RunJournal.prepared before request
  have converted := convertRoot_eq_convertHeap before.comparator.externalDepth source before.next before.blocks
  change convertRoot before.comparator.externalDepth source (rootNames source before.next)
    (rootNames source before.next) before.blocks = prepared at converted
  have labelsEqual : labels before.comparator K before.blocks = labels before.comparator K prepared := by
    funext record
    change GreedyMerge.StateLabels.label _ _ _ record.val = GreedyMerge.StateLabels.label _ _ _ record.val
    rw [← converted, convertRoot_labels]
  have preparedSound : LabelSnapshots.Sound before.comparator K before.clock prepared old :=
    ⟨sound.before, sound.current.trans labelsEqual, LabelSnapshots.convertHeap_snapshots _ selected before.next before.blocks sound.snapshots⟩
  have ready : Ready before.comparator before.refined.tree prepared := by
    rw [← converted]
    exact convertRoot_ready _ _ _ _ _ _ valid.1
  have empty : ∀ side, growerEntries (prepared source side).grower = [] := by
    intro side
    rw [← converted]
    exact convertRoot_empty _ _ _ _ _ side
  have temporal : BeforeTime before.clock prepared := by
    intro owner side entry member
    rw [← converted, convertRoot_entries] at member
    exact ((chronology_iff ..).mp valid.2.1).2 owner side entry member
  let sourceSide := fun event : External n × External n => decide (event.2.val < source.val)
  have whole := LabelSnapshots.access_sound before.comparator K source sourceSide before.clock prepared data.events old
    preparedSound temporal (GrowthJournal.convertHeap_creators _ selected before.next before.blocks creators)
  have journal := AccessJournal.actual_history_agrees data source
    (AccessTrace.geometry data source rfl (Greedy.Execution.root_minimum _ request root)) K before.clock prepared ready empty
    state (agree.trans labelsEqual) old (sound.current.trans agree.symm)
  exact ⟨_, whole.1, LabelSnapshots.access_future before.comparator K source sourceSide before.clock prepared data.events old, journal.2⟩

end Greedy.AccessPrograms
