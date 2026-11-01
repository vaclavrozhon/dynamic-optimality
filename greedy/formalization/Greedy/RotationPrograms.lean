import Greedy.RotationJournal
import Greedy.AdministrationVariation
import Greedy.RunLabelHistory
import Greedy.PreparationMemory
import Greedy.TicketRealizes

/-!
Joint history and journal witnesses for retained refinement rotations.
The execution witness is a proposition, so its concrete journals and
histories are constructed together under an existential quantifier.
-/

namespace Greedy.RotationPrograms

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open EntryJournal RestorationJournal AdministrationJournal FreshRecanonicalization

theorem refinement_joint {n count : ℕ} (comparator : BST 0 n) (H : ℕ)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H)
    {first last : Frame n} {births : List ℕ}
    (execution : FreshRecanonicalization.Execution comparator
      (Greedy.Execution.entryReader comparator (contractedGap H)) count first last births)
    (state : WeightedMemory.State (External n)) (old : LabelHistory.History (External n))
    (agree : state.label = labels comparator (contractedGap H) first.states)
    (sound : LabelSnapshots.Sound comparator (contractedGap H) first.clock first.states old)
    (chronology : GreedyMerge.ActualLinks.Chronology first.clock first.states)
    (ordered : GreedyMerge.ActualLinks.Ordered first.states)
    (synced : LiveMemory.Synced state.memory first.states) :
    ∃ actions : List (Action (External n)), ∃ history : LabelHistory.History (External n),
      LabelSnapshots.Sound comparator (contractedGap H) last.clock last.states history ∧
      GreedyMerge.ActualLinks.Chronology last.clock last.states ∧
      LabelHistory.Future old history first.clock ∧ first.clock ≤ last.clock ∧
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels comparator (contractedGap H) last.states ∧
      total ordinary state actions ≤ 4*count ∧
      total positiveChange state actions ≤ 8*((contractedGap H : ℤ)-1)*count ∧
      OrdinaryOnly actions ∧
      LabelHistory.variation history = LabelHistory.variation old + total absoluteChange state actions ∧
      LiveMemory.Synced (run state actions).memory last.states ∧
      TicketJournal.Realizes first.states last.states actions := by
  induction execution generalizing state old with
  | nil =>
      exact ⟨[], old, sound, chronology, .refl _ _, le_refl _, trivial, agree,
        by simp [total], by simp [total], by simp [OrdinaryOnly], by simp [total], synced, TicketJournal.Realizes.nil _⟩
  | @cons count depth first last middle births rotation rest ih =>
      let ports := refinementRotationPorts (Snapshot.ofTree comparator) rotation
      let head := AdministrationJournal.refinement comparator middle (contractedGap H) ports
        (Greedy.Execution.entryReader comparator (contractedGap H) first.clock) first.next first.states
      let middleHistory := LabelSnapshots.refinementHistory comparator middle (contractedGap H)
        ports first.clock first.next first.states old
      have headSpec := AdministrationJournal.refinement_spec comparator middle H height ports
        (Greedy.Execution.entryReader comparator (contractedGap H) first.clock) (fun _ _ _ _ => rfl)
        first.next first.states state agree
      have headSound := LabelSnapshots.refinement_sound comparator middle (contractedGap H) ports
        (refinementRotationPorts_spec _ rotation).2.1 first.clock first.next first.states old sound chronology
      have headVariation := AdministrationJournal.refinement_agrees comparator middle (contractedGap H) ports
        first.clock first.next first.states state old (sound.current.trans agree.symm)
      have headMemory := LiveMemory.refinement comparator middle (contractedGap H) ports
        (refinementRotationPorts_spec _ rotation).1 first.clock first.next first.states ordered state synced
      obtain ⟨tail, history, finalSound, finalChronology, future, advances, valid, tailLabels, ordinaryTail, positiveTail, kinds, variation, finalMemory, tailRealizes⟩ :=
        ih (run state head) middleHistory headSpec.2.1 headSound.1 headSound.2 headMemory.2 headMemory.1
      have advance : first.clock ≤ (nextFrame comparator
          (Greedy.Execution.entryReader comparator (contractedGap H)) first middle rotation).clock := by
        change first.clock ≤ first.clock+5; omega
      have few : (ports.length : ℤ) ≤ 4 := by exact_mod_cast (refinementRotationPorts_spec _ rotation).2.1
      have cap : 0 ≤ (contractedGap H : ℤ)-1 := by unfold contractedGap; omega
      refine ⟨head ++ tail, history, finalSound, finalChronology,
        (LabelSnapshots.refinement_future comparator middle (contractedGap H) ports first.clock first.next first.states old).trans
          (future.weaken first.clock advance), advance.trans advances,
        (valid_append ..).mpr ⟨headSpec.1, valid⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run_append]; exact tailLabels
      · rw [total_append]
        have bound : total ordinary state head ≤ ports.length := headSpec.2.2.1
        push_cast
        linarith
      · rw [total_append]
        have bound : total positiveChange state head ≤ 2*((contractedGap H : ℤ)-1)*ports.length := headSpec.2.2.2
        push_cast
        nlinarith
      · exact (ordinaryOnly_append ..).mpr ⟨by apply AdministrationKinds.refinement_ordinary, kinds⟩
      · rw [total_append, variation]
        change LabelHistory.variation middleHistory + _ = _
        rw [show LabelHistory.variation middleHistory = LabelHistory.variation old + total absoluteChange state head from headVariation.2.2]
        exact add_assoc _ _ _
      · rw [run_append]; exact finalMemory
      · apply TicketJournal.Realizes.append (second := tail) _ tailRealizes
        intro rich pointer
        exact ⟨TicketJournal.refinement comparator middle (contractedGap H) ports first.clock first.next first.states,
          TicketJournal.refinement_erases .., TicketJournal.refinement_administrative _ _ _ _ _ _ _,
          TicketJournal.refinement_pointer comparator middle (contractedGap H) ports
            (refinementRotationPorts_spec _ rotation).1 first.clock first.next first.states ordered rich pointer⟩

theorem rotation_joint {n depth : ℕ} (before : Greedy.Execution.State n) (after : BST 0 n)
    (rotation : RotationAt depth before.comparator after) (H : ℕ)
    (oldHeight : before.comparator.height ≤ H) (height : after.height ≤ H)
    (valid : before.Valid) (data : Greedy.Execution.RotationData before after rotation (contractedGap H))
    (state : WeightedMemory.State (External n)) (old : LabelHistory.History (External n))
    (agree : state.label = labels before.comparator (contractedGap H) before.blocks)
    (sound : LabelSnapshots.Sound before.comparator (contractedGap H) before.clock before.blocks old)
    (synced : LiveMemory.Synced state.memory before.blocks) :
    ∃ actions : List (Action (External n)), ∃ history : LabelHistory.History (External n),
      LabelSnapshots.Sound after (contractedGap H) data.state.clock data.state.blocks history ∧
      LabelHistory.Future old history before.clock ∧ before.clock ≤ data.state.clock ∧
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels after (contractedGap H) data.state.blocks ∧
      total ordinary state actions ≤ 11 ∧ total positiveChange state actions ≤ 22*((contractedGap H : ℤ)-1) ∧
      OrdinaryOnly actions ∧ LabelHistory.variation history = LabelHistory.variation old + total absoluteChange state actions ∧
      LiveMemory.Synced (run state actions).memory data.state.blocks ∧
      TicketJournal.Realizes before.blocks data.state.blocks actions := by
  let input := comparatorInput rotation
  let plan := GreedyMerge.ComparatorOuter.rotationPlan input.step before.refined.tree
  let reader := Greedy.Execution.entryReader after (contractedGap H) before.clock
  let head := planJournal input.profile before.refined.tree plan (contractedGap H) reader before.next before.blocks
  let middleHistory := LabelSnapshots.planHistory input.profile before.refined.tree plan (contractedGap H)
    before.clock before.next before.blocks old
  have oldRanks : ∀ record : External n, before.comparator.externalDepth record.val ≤ H :=
    fun record => (externalDepth_le_height before.comparator record.val).trans oldHeight
  have ranks : ∀ record : External n, after.externalDepth record.val ≤ H :=
    fun record => (externalDepth_le_height after record.val).trans height
  have headSpec := plan_spec input.step input.profile before.refined.tree plan H oldRanks ranks reader
    (fun _ _ _ _ => rfl) before.next before.blocks valid.1 state agree
  have headSound := LabelSnapshots.plan_sound input.profile before.refined.tree plan (contractedGap H)
    before.clock before.next before.blocks old sound valid.2.1
  have headVariation := plan_agrees input.profile before.refined.tree plan (contractedGap H)
    before.clock before.next before.blocks state old (sound.current.trans agree.symm)
  have headMemory := LiveMemory.plan input.step input.profile before.refined.tree plan (contractedGap H)
    before.clock before.next before.blocks valid.1 state synced
  obtain ⟨tail, history, finalSound, _chronology, future, advances, tailValid, tailLabels, ordinaryTail, positiveTail, kinds, variation, finalMemory, tailRealizes⟩ :=
    refinement_joint after H ranks data.executed (run state head) middleHistory headSpec.2.1 headSound.1 headSound.2 headMemory.2 headMemory.1
  have advance : before.clock ≤ (Greedy.Execution.rotationPrefix before after rotation (contractedGap H)).clock := by
    change before.clock ≤ before.clock+4; omega
  have few : (data.steps : ℤ) ≤ 2 := by exact_mod_cast data.fewSteps
  have cap : 0 ≤ (contractedGap H : ℤ)-1 := by unfold contractedGap; omega
  refine ⟨head ++ tail, history, finalSound,
    (LabelSnapshots.plan_future input.profile before.refined.tree plan (contractedGap H) before.clock before.next before.blocks old).trans
      (future.weaken before.clock advance), advance.trans advances,
    (valid_append ..).mpr ⟨headSpec.1, tailValid⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_append]; exact tailLabels
  · rw [total_append]
    have bound : total ordinary state head ≤ 3 := headSpec.2.2.1
    linarith
  · rw [total_append]
    have bound : total positiveChange state head ≤ 6*((contractedGap H : ℤ)-1) := headSpec.2.2.2
    nlinarith
  · exact (ordinaryOnly_append ..).mpr ⟨by apply AdministrationKinds.plan_ordinary, kinds⟩
  · rw [total_append, variation]
    change LabelHistory.variation middleHistory + _ = _
    rw [show LabelHistory.variation middleHistory = LabelHistory.variation old + total absoluteChange state head from headVariation.2.2]
    exact add_assoc _ _ _
  · rw [run_append]; exact finalMemory
  · apply TicketJournal.Realizes.append (second := tail) _ tailRealizes
    intro rich pointer
    exact ⟨TicketJournal.plan input.profile before.refined.tree plan (contractedGap H) before.clock before.next before.blocks,
      TicketJournal.plan_erases .., TicketJournal.plan_administrative _ _ _ _ _ _ _,
      TicketJournal.plan_pointer input.step input.profile before.refined.tree plan (contractedGap H)
        before.clock before.next before.blocks valid.1 rich pointer⟩

end Greedy.RotationPrograms
