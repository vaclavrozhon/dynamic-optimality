import Greedy.AdministrationKinds
import Greedy.ExecutionRotation

/-!
# One complete comparator rotation in the chronological journal

This includes the literal comparator macro and every recanonicalization
step retained by `Execution.RotationData`. A complete rotation introduces
at most eleven ordinary entries and positive label variation at most
`22 * (K - 1)`, where `K` is the contracted height bound.
-/

namespace Greedy.RotationJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open EntryJournal RestorationJournal AdministrationJournal FreshRecanonicalization

/-- All refinement steps refer to the same comparator and the exact
states retained by the fresh execution witness. -/
theorem refinement_execution {n count : ℕ} (comparator : BST 0 n) (H : ℕ)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H)
    (reader : Reader n)
    (readerKey : ∀ clock stage states record owner, (reader clock stage states record owner).key = record.val)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator reader count first last births)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator (contractedGap H) first.states) :
    ∃ actions : List (Action (External n)),
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels comparator (contractedGap H) last.states ∧
      total ordinary state actions ≤ 4 * count ∧
      total positiveChange state actions ≤ 8 * ((contractedGap H : ℤ) - 1) * count ∧
      OrdinaryOnly actions := by
  induction execution generalizing state with
  | nil frame => exact ⟨[], trivial, agree, by simp [total], by simp [total], by simp [OrdinaryOnly]⟩
  | @cons count depth first last middle births rotation rest ih =>
      let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
      let head := AdministrationJournal.refinement comparator middle (contractedGap H) ports
        (reader first.clock) first.next first.states
      have firstSpec := refinement_spec comparator middle H height ports (reader first.clock)
        (readerKey first.clock) first.next first.states state agree
      obtain ⟨tail, tailValid, tailLabels, tailOrdinary, tailPositive, tailKinds⟩ :=
        ih (run state head) firstSpec.2.1
      have few : ports.length ≤ 4 := (refinementRotationPorts_spec (Snapshot.ofTree comparator) rotation).2.1
      have cast : (ports.length : ℤ) ≤ 4 := by exact_mod_cast few
      have cap : 0 ≤ (contractedGap H : ℤ) - 1 := by unfold contractedGap; omega
      refine ⟨head ++ tail, (valid_append ..).mpr ⟨firstSpec.1, tailValid⟩, ?_, ?_, ?_, ?_⟩
      · rw [run_append]; exact tailLabels
      · rw [total_append]
        change total ordinary state head + total ordinary (run state head) tail ≤ _
        have ordinaryHead : total ordinary state head ≤ ports.length := firstSpec.2.2.1
        push_cast
        linarith
      · rw [total_append]
        have bound : total positiveChange state head ≤ 2 * ((contractedGap H : ℤ) - 1) * ports.length := firstSpec.2.2.2
        push_cast
        nlinarith
      · exact (ordinaryOnly_append ..).mpr ⟨by apply AdministrationKinds.refinement_ordinary, tailKinds⟩

/-- The local port bounds are derived from the actual rotation, including
its at-most-two refinement rotations; they are not supplied by the caller. -/
theorem complete_rotation {n depth : ℕ} (before : Greedy.Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (H : ℕ)
    (oldHeight : before.comparator.height ≤ H) (height : after.height ≤ H)
    (valid : before.Valid) (data : Greedy.Execution.RotationData before after rotation (contractedGap H))
    (state : WeightedMemory.State (External n))
    (agree : state.label = labels before.comparator (contractedGap H) before.blocks) :
    ∃ actions : List (Action (External n)),
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels after (contractedGap H) data.state.blocks ∧
      total ordinary state actions ≤ 11 ∧
      total positiveChange state actions ≤ 22 * ((contractedGap H : ℤ) - 1) ∧
      OrdinaryOnly actions := by
  let input := comparatorInput rotation
  let reader := Greedy.Execution.entryReader after (contractedGap H) before.clock
  let head := planJournal input.profile before.refined.tree
    (GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree) (contractedGap H)
    reader before.next before.blocks
  have oldRanks : ∀ record : External n, before.comparator.externalDepth record.val ≤ H :=
    fun record => (externalDepth_le_height before.comparator record.val).trans oldHeight
  have ranks : ∀ record : External n, after.externalDepth record.val ≤ H :=
    fun record => (externalDepth_le_height after record.val).trans height
  have first := plan_spec input.step input.profile before.refined.tree
    (GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree) H oldRanks ranks reader
    (fun _ _ _ _ => rfl) before.next before.blocks valid.1 state agree
  obtain ⟨tail, tailValid, tailLabels, tailOrdinary, tailPositive, tailKinds⟩ :=
    refinement_execution after H ranks (Greedy.Execution.entryReader after (contractedGap H))
      (fun _ _ _ _ _ => rfl) data.executed (run state head) first.2.1
  have few : (data.steps : ℤ) ≤ 2 := by exact_mod_cast data.fewSteps
  have cap : 0 ≤ (contractedGap H : ℤ) - 1 := by unfold contractedGap; omega
  refine ⟨head ++ tail, (valid_append ..).mpr ⟨first.1, tailValid⟩, ?_, ?_, ?_, ?_⟩
  · rw [run_append]; exact tailLabels
  · rw [total_append]
    have ordinaryHead : total ordinary state head ≤ 3 := first.2.2.1
    linarith
  · rw [total_append]
    have positiveHead : total positiveChange state head ≤ 6 * ((contractedGap H : ℤ) - 1) := first.2.2.2
    nlinarith

  · exact (ordinaryOnly_append ..).mpr ⟨by apply AdministrationKinds.plan_ordinary, tailKinds⟩

end Greedy.RotationJournal
