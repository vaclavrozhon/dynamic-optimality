import Greedy.HistoryAdministration
import Greedy.HistoryAccess
import Greedy.HistoryExtension
import Greedy.RunGrowthInvariant

/-!
# Label snapshots throughout a literal shared execution

The final sparse history is constructed from the retained comparator and
access operations. Its current labels equal the actual final block labels,
and every stored immutable entry reads this history at its original time.
-/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.GrowthBook
open FreshRecanonicalization

theorem refinement_execution_sound {n count : ℕ} (comparator : BST 0 n) (K : ℤ)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator (Greedy.Execution.entryReader comparator K) count first last births)
    (history : LabelHistory.History (External n)) (sound : Sound comparator K first.clock first.states history)
    (chronology : Chronology first.clock first.states) :
    ∃ finalHistory, Sound comparator K last.clock last.states finalHistory ∧ Chronology last.clock last.states ∧
      LabelHistory.Future history finalHistory first.clock ∧ first.clock ≤ last.clock := by
  induction execution generalizing history with
  | nil => exact ⟨history, sound, chronology, .refl _ _, le_refl _⟩
  | @cons count depth first last middle births rotation rest ih =>
      have head := refinement_sound comparator middle K
        (refinementRotationPorts (Splay.Rank.Snapshot.ofTree comparator) rotation)
        (refinementRotationPorts_spec _ rotation).2.1 first.clock first.next first.states history sound chronology
      obtain ⟨finalHistory, finalSound, finalChronology, tail, later⟩ := ih _ head.1 head.2
      have advance : first.clock ≤ (nextFrame comparator (Greedy.Execution.entryReader comparator K) first middle rotation).clock := by
        change first.clock ≤ first.clock+5
        omega
      exact ⟨finalHistory, finalSound, finalChronology,
        (refinement_future comparator middle K _ first.clock first.next first.states history).trans
          (tail.weaken first.clock advance), advance.trans later⟩

theorem complete_rotation_sound {n depth : ℕ} (before : Greedy.Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (K : ℤ)
    (data : Greedy.Execution.RotationData before after rotation K)
    (history : LabelHistory.History (External n))
    (sound : Sound before.comparator K before.clock before.blocks history)
    (chronology : Chronology before.clock before.blocks) :
    ∃ finalHistory, Sound after K data.state.clock data.state.blocks finalHistory ∧
      LabelHistory.Future history finalHistory before.clock ∧ before.clock ≤ data.state.clock := by
  let input := comparatorInput rotation
  let plan := GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree
  have head := plan_sound input.profile before.refined.tree plan K before.clock before.next before.blocks history sound chronology
  obtain ⟨finalHistory, finalSound, _, tail, later⟩ := refinement_execution_sound after K data.executed _ head.1 head.2
  have advance : before.clock ≤ (Greedy.Execution.rotationPrefix before after rotation K).clock := by
    change before.clock ≤ before.clock+4
    omega
  exact ⟨finalHistory, finalSound,
    (plan_future input.profile before.refined.tree plan K before.clock before.next before.blocks history).trans
      (tail.weaken before.clock advance), advance.trans later⟩

theorem afterAccess_sound {n : ℕ} (before : Greedy.Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : GreedyMerge.PathPlateau.Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Greedy.Execution.afterRefinement before request).tree decomposition)
    (history : LabelHistory.History (External n))
    (sound : Sound before.comparator K before.clock before.blocks history)
    (temporal : BeforeTime before.clock before.blocks) (creators : GrowthJournal.Creators before.blocks) :
    ∃ finalHistory, Sound before.comparator K (Greedy.Execution.afterAccess before request K decomposition data).clock
      (Greedy.Execution.afterAccess before request K decomposition data).blocks finalHistory ∧
      LabelHistory.Future history finalHistory before.clock := by
  let selected := fun (owner : External n) (_ : Bool) => decide (owner = Greedy.Execution.source request)
  let prepared := (convertHeap before.comparator.externalDepth selected before.next before.blocks).1
  have equal := convertRoot_eq_convertHeap before.comparator.externalDepth (Greedy.Execution.source request) before.next before.blocks
  change convertRoot before.comparator.externalDepth (Greedy.Execution.source request)
    (rootNames (Greedy.Execution.source request) before.next) (rootNames (Greedy.Execution.source request) before.next)
    before.blocks = prepared at equal
  have current : LabelHistory.current history = RestorationJournal.labels before.comparator K prepared := by
    rw [sound.current]
    funext record
    change GreedyMerge.StateLabels.label _ _ _ record.val = GreedyMerge.StateLabels.label _ _ _ record.val
    rw [← equal, convertRoot_labels]
  have preparedSound : Sound before.comparator K before.clock prepared history :=
    ⟨sound.before, current, convertHeap_snapshots _ selected before.next before.blocks sound.snapshots⟩
  have preparedTime : BeforeTime before.clock prepared := by
    intro owner side entry member
    rw [← equal, convertRoot_entries] at member
    exact temporal owner side entry member
  have complete := access_sound before.comparator K (Greedy.Execution.source request)
    (fun event => decide (event.2.val < (Greedy.Execution.source request).val)) before.clock prepared data.events history
    preparedSound preparedTime (GrowthJournal.convertHeap_creators _ selected before.next before.blocks creators)
  exact ⟨_, complete.1, access_future before.comparator K (Greedy.Execution.source request) _ before.clock prepared data.events history⟩

theorem exists_sound {n : ℕ} {K : ℤ} {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K first last requests) (valid : first.Valid)
    (books : HeapBooks n) (growth : GrowthJournal.Invariant first.clock first.next first.blocks books)
    (history : LabelHistory.History (External n)) (sound : Sound first.comparator K first.clock first.blocks history) :
    ∃ finalHistory, Sound last.comparator K last.clock last.blocks finalHistory ∧
      LabelHistory.Future history finalHistory first.clock := by
  induction execution generalizing books history with
  | done => exact ⟨history, sound, .refl _ _⟩
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      obtain ⟨nextHistory, nextSound, head, advance⟩ := complete_rotation_sound first after rotation K data history sound valid.2.1
      obtain ⟨nextBooks, nextGrowth, _⟩ := GrowthJournal.complete_rotation_history first after rotation K data books growth
      obtain ⟨finalHistory, finalSound, tail⟩ := ih afterValid nextBooks nextGrowth nextHistory nextSound
      exact ⟨finalHistory, finalSound, head.trans (tail.weaken first.clock advance)⟩
  | @access first last requests request root decomposition data afterValid rest ih =>
      obtain ⟨nextHistory, nextSound, head⟩ := afterAccess_sound first request K decomposition data history sound
        ((chronology_iff ..).mp valid.2.1).2 growth.creators
      obtain ⟨nextBooks, nextGrowth, _⟩ := GrowthJournal.access_history first request K decomposition data books growth
      obtain ⟨finalHistory, finalSound, tail⟩ := ih afterValid nextBooks nextGrowth nextHistory nextSound
      have advance : first.clock ≤ (Greedy.Execution.afterAccess first request K decomposition data).clock := Nat.le_add_right _ _
      exact ⟨finalHistory, finalSound, head.trans (tail.weaken first.clock advance)⟩

/-- No label-history certificate is an input: initialization and every
actual execution operation produce the history and its snapshot proof. -/
theorem initialized_sound {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Greedy.Execution.State n} {requests : List (Fin n)}
    (execution : Greedy.Execution.Run K (Greedy.Execution.initial initial comparator K) last requests) :
    ∃ history, Sound last.comparator K last.clock last.blocks history := by
  obtain ⟨history, sound, _⟩ := exists_sound execution (Greedy.Execution.initial_valid initial comparator K)
    (GreedyMerge.GrowthBook.initial (Splay.Rank.Snapshot.ofTree comparator)
      (Greedy.Execution.initial initial comparator K).refined.tree K)
    (GrowthJournal.initial_invariant (Splay.Rank.Snapshot.ofTree comparator) _ K) _
    (initial_sound comparator _ K)
  exact ⟨history, sound⟩

end Greedy.LabelSnapshots
