import Greedy.RotationPrograms
import Greedy.AccessPrograms
import Greedy.HistoricalSnapshots
import Greedy.AccessMeasurements
import Greedy.BoundaryMeasurements
import Greedy.GoodMeasurements
import Greedy.NegativeMeasurements
import Greedy.PositiveMeasurements
import Greedy.AccessMemory
import Greedy.LoserShift
import Greedy.CreatorMemoryMeasurements
import Greedy.RunShiftTelescope
import Greedy.TicketCertificates
import Greedy.TicketPhaseMeasurements

/-!
A single constructed journal and sparse history for the whole run.
Every past source snapshot and both variation totals refer to these
same witnesses, including across comparator administration.
-/

namespace Greedy.JointRunJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.GrowthBook
open EntryJournal RestorationJournal

theorem exists_joint {n : ℕ} {first last : Greedy.Execution.State n} {requests : List (Fin n)}
    (H : ℕ) (execution : Greedy.Execution.Run (contractedGap H) first last requests)
    (bounded : execution.Bounded H) (valid : first.Valid)
    (books : HeapBooks n) (growth : GrowthJournal.Invariant first.clock first.next first.blocks books)
    (state : WeightedMemory.State (External n)) (old : LabelHistory.History (External n))
    (agree : state.label = labels first.comparator (contractedGap H) first.blocks)
    (sound : LabelSnapshots.Sound first.comparator (contractedGap H) first.clock first.blocks old)
    (synced : LiveMemory.Synced state.memory first.blocks)
    (pointer : External n → MembershipPointer.Ticket)
    (pointerSync : MembershipPointer.Synced pointer first.blocks) :
    ∃ actions : List (Action (External n)), ∃ history : LabelHistory.History (External n),
      LabelSnapshots.Sound last.comparator (contractedGap H) last.clock last.blocks history ∧
      LabelHistory.Future old history first.clock ∧ LabelSnapshots.AllSourcesSnapshots history execution ∧
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels last.comparator (contractedGap H) last.blocks ∧
      total ordinary state actions ≤ 11*execution.rotations ∧
      total internal state actions + total boundary state actions = execution.links ∧
      LabelHistory.variation history = LabelHistory.variation old + total absoluteChange state actions ∧
      total positiveChange state actions ≤ InstanceCharge.mass (DepartureAmounts.charge .increase (contractedGap H)) execution +
        22*((contractedGap H : ℤ)-1)*execution.rotations ∧
      total boundary state actions ≤ total negativeChange state actions +
        InstanceCharge.mass (DepartureAmounts.charge .boundary (contractedGap H)) execution ∧
      total good state actions ≤ total negativeChange state actions ∧
      total negativeEntry state actions ≤ 4*total negativeChange state actions +
        InstanceCharge.mass (IncomingExcess.charge (contractedGap H)) execution ∧
      total positiveEntry state actions ≤ total negativeChange state actions +
        InstanceCharge.mass (OutgoingExcess.charge .nonrootWinner (contractedGap H)) execution +
        InstanceCharge.mass (OutgoingExcess.charge .rootLoser (contractedGap H)) execution ∧
      LiveMemory.Synced (run state actions).memory last.blocks ∧
      total shift state actions = LoserShift.sum execution ∧
      total creatorShift state actions = CreatorPhase.shiftTotal execution ∧
      TicketJournal.Certifies state pointer last.blocks actions (fun ticket => WinnerTickets.total execution ticket.1 ticket.2) := by
  induction execution generalizing books state old pointer with
  | done => exact ⟨[], old, sound, .refl _ _, sound.snapshots, trivial, agree,
      by simp [total, Greedy.Execution.Run.rotations], by simp [total, Greedy.Execution.Run.links], by simp [total],
      by simp [total, InstanceCharge.mass, Greedy.Execution.Run.rotations], by simp [total, InstanceCharge.mass], le_refl _,
      by simp [total, InstanceCharge.mass], by simp [total, InstanceCharge.mass], synced, rfl, rfl, TicketJournal.certifies_nil state pointer _ pointerSync⟩
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      obtain ⟨head, middleHistory, middleSound, headFuture, advance, headValid, headLabels, headOrdinary, headPositive, headKinds, headVariation, headMemory, headRealizes⟩ :=
        RotationPrograms.rotation_joint first after rotation H bounded.1 (RunJournal.initial_height rest H bounded.2)
          valid data state old agree sound synced
      obtain ⟨headRich, headErase, headAdmin, headPointer⟩ := headRealizes ⟨state, pointer⟩ pointerSync
      obtain ⟨nextBooks, nextGrowth, _⟩ := GrowthJournal.complete_rotation_history first after rotation (contractedGap H) data books growth
      obtain ⟨tail, history, finalSound, tailFuture, sources, tailValid, tailLabels, tailOrdinary, tailCount, tailVariation, tailPositive, tailBoundary, tailGood, tailNegativeEntry, tailPositiveEntry, finalMemory, tailShift, tailCreator, tailCertificate⟩ :=
        ih bounded.2 afterValid nextBooks nextGrowth (run state head) middleHistory headLabels middleSound headMemory (WinnerCredit.run ⟨state, pointer⟩ headRich).ticket headPointer
      have extension := headFuture.trans (tailFuture.weaken first.clock advance)
      have temporal := ((chronology_iff ..).mp (valid.2.1.mono (Nat.le_succ first.clock))).2
      refine ⟨head ++ tail, history, finalSound, extension, ⟨sound.snapshots.future extension temporal, sources⟩,
        (valid_append ..).mpr ⟨headValid, tailValid⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run_append]; exact tailLabels
      · rw [total_append]
        simp only [Greedy.Execution.Run.rotations, Nat.cast_add, Nat.cast_one]
        linarith
      · rw [total_append, total_append, ordinaryOnly_internal_zero state head headKinds,
          ordinaryOnly_boundary_zero state head headKinds, zero_add, zero_add]
        exact tailCount
      · rw [total_append, tailVariation, headVariation]
        exact add_assoc _ _ _
      · rw [total_append]
        simp only [InstanceCharge.mass, Greedy.Execution.Run.rotations, Nat.cast_add, Nat.cast_one]
        linarith
      · rw [total_append, ordinaryOnly_boundary_zero state head headKinds, zero_add, total_append]
        have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state head
        change _ ≤ _ + _ + InstanceCharge.mass (DepartureAmounts.charge .boundary (contractedGap H)) rest
        linarith
      · rw [total_append, ordinaryOnly_total_zero good (by intros; rfl) (by intros; rfl) state head headKinds, zero_add, total_append]
        have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state head
        linarith
      · rw [total_append, ordinaryOnly_total_zero negativeEntry (by intros; rfl) (by intros; rfl) state head headKinds, zero_add, total_append]
        have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state head
        simp only [InstanceCharge.mass]
        linarith
      · rw [total_append, ordinaryOnly_total_zero positiveEntry (by intros; rfl) (by intros; rfl) state head headKinds, zero_add, total_append]
        have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state head
        simp only [InstanceCharge.mass]
        linarith
      · rw [run_append]; exact finalMemory
      · rw [total_append, ordinaryOnly_total_zero shift (by intros; rfl) (by intros; rfl) state head headKinds, zero_add]
        exact tailShift
      · rw [total_append, ordinaryOnly_total_zero creatorShift (by intros; rfl) (by intros; rfl) state head headKinds, zero_add]
        exact tailCreator
      · simpa only [Nat.zero_add, WinnerTickets.total] using
          TicketJournal.certifies_append state pointer last.blocks head tail (fun _ => 0)
            (fun ticket => WinnerTickets.total rest ticket.1 ticket.2) headRich headErase
            (headAdmin.legal _) headAdmin.paired (headAdmin.remaining_zero) tailCertificate
  | @access first last requests request root decomposition data afterValid rest ih =>
      let head := RunJournal.access first request decomposition data
      have headSpec := RunJournal.access_spec first request decomposition data H bounded.1 valid root state agree
      obtain ⟨middleHistory, middleSound, headFuture, headVariation⟩ :=
        AccessPrograms.access_joint first request (contractedGap H) decomposition data valid root growth.creators state old agree sound
      obtain ⟨nextBooks, nextGrowth, _⟩ := GrowthJournal.access_history first request (contractedGap H) decomposition data books growth
      have headMemory := LiveMemory.access first request (contractedGap H) root decomposition data valid state agree synced
      let headRich := TicketJournal.access first request (contractedGap H) decomposition data pointer
      have headErase : WinnerCredit.erase headRich = head := TicketJournal.access_erases ..
      have headCorrect := TicketJournal.access_correct first request (contractedGap H) root decomposition data valid ⟨state, pointer⟩ agree pointerSync
      have headPointer := headCorrect.2
      obtain ⟨tail, history, finalSound, tailFuture, sources, tailValid, tailLabels, tailOrdinary, tailCount, tailVariation, tailPositive, tailBoundary, tailGood, tailNegativeEntry, tailPositiveEntry, finalMemory, tailShift, tailCreator, tailCertificate⟩ :=
        ih bounded.2 afterValid nextBooks nextGrowth (run state head) middleHistory headSpec.2.1 middleSound headMemory (WinnerCredit.run ⟨state, pointer⟩ headRich).ticket headPointer
      have advance : first.clock ≤ (Greedy.Execution.afterAccess first request (contractedGap H) decomposition data).clock := Nat.le_add_right _ _
      have extension := headFuture.trans (tailFuture.weaken first.clock advance)
      have temporal := ((chronology_iff ..).mp (valid.2.1.mono (Nat.le_succ first.clock))).2
      have snapshots := sound.snapshots.future extension temporal
      refine ⟨head ++ tail, history, finalSound, extension,
        ⟨snapshots, LabelSnapshots.convertHeap_snapshots _ _ first.next first.blocks snapshots, sources⟩,
        (valid_append ..).mpr ⟨headSpec.1, tailValid⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [run_append]; exact tailLabels
      · rw [total_append]
        have zero : total ordinary state head = 0 := headSpec.2.2
        rw [zero, zero_add]
        exact tailOrdinary
      · rw [total_append, total_append]
        have headCount : total internal state head + total boundary state head = data.events.length :=
          AccessJournal.program_link_count _ _ data.events (fun event _ => AccessTrace.kind_not_ordinary _ _ event) state
        simp only [Greedy.Execution.Run.links, Nat.cast_add]
        linarith
      · rw [total_append, tailVariation, headVariation]
        exact add_assoc _ _ _
      · rw [total_append]
        have headPositive := RunJournal.access_positive_eq first request (contractedGap H) root decomposition data valid state agree
        change total positiveChange state head = _ at headPositive
        rw [headPositive]
        change _ ≤ _ + InstanceCharge.mass (DepartureAmounts.charge .increase (contractedGap H)) rest + _
        simp only [Greedy.Execution.Run.rotations]
        linarith
      · rw [total_append, total_append]
        have headBoundary := RunJournal.access_boundary_bound first request (contractedGap H) root decomposition data valid state agree
        change total boundary state head ≤ total negativeChange state head + _ at headBoundary
        simp only [InstanceCharge.mass]
        linarith
      · rw [total_append, total_append]
        have headGood := RunJournal.access_good_bound first request (contractedGap H) root decomposition data valid state agree
        change total good state head ≤ total negativeChange state head at headGood
        linarith
      · rw [total_append, total_append]
        have headNegative := RunJournal.access_negative_entry_bound first request (contractedGap H) root decomposition data valid state agree
        change total negativeEntry state head ≤ 4*total negativeChange state head + _ at headNegative
        simp only [InstanceCharge.mass]
        linarith
      · rw [total_append, total_append]
        have headPositiveEntry := RunJournal.access_positive_entry_bound first request (contractedGap H) root decomposition data valid state agree
        change total positiveEntry state head ≤ total negativeChange state head + _ + _ at headPositiveEntry
        simp only [InstanceCharge.mass]
        linarith
      · rw [run_append]; exact finalMemory
      · rw [total_append, tailShift]
        exact congrArg (fun value => value + LoserShift.sum rest)
          (LoserShift.access_eq first request (contractedGap H) root decomposition data state agree synced)
      · rw [total_append, tailCreator]
        exact congrArg (fun value => value + CreatorPhase.shiftTotal rest)
          (RunJournal.access_creator_eq first request (contractedGap H) root decomposition data valid state synced)
      · exact TicketJournal.certifies_append state pointer last.blocks head tail
          (fun ticket => WinnerTickets.familyWins data (RunJournal.prepared first request) (Greedy.Execution.source request) ticket.1 ticket.2)
          (fun ticket => WinnerTickets.total rest ticket.1 ticket.2) headRich headErase headCorrect.1
          (TicketJournal.access_paired ..)
          (TicketJournal.access_remaining first request (contractedGap H) root decomposition data valid pointer pointerSync)
          tailCertificate

end Greedy.JointRunJournal
