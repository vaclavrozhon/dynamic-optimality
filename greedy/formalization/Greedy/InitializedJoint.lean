import Greedy.JointRunJournal
import Greedy.InitialJournal
import Greedy.RunShiftTelescope
import Greedy.TicketInitial

/-!
The initialized entry journal and immutable history are constructed
together. Actual creator shifts are bounded by the positive and negative
variation measured in this very journal.
-/

namespace Greedy.InitialJournal

open EntryJournal

theorem install_absolute_zero {Record : Type*} [Fintype Record] [DecidableEq Record]
    (parent : Record → Option Record) (records : List Record) (state : WeightedMemory.State Record) :
    total absoluteChange state (install parent records) = 0 := by
  induction records generalizing state with
  | nil => rfl
  | cons record rest ih =>
      cases relation : parent record with
      | none => simpa only [install, relation, List.nil_append] using ih state
      | some owner =>
          simpa only [install, relation, List.singleton_append, total, absoluteChange, zero_add] using
            ih (step state (.entry record owner .ordinary))

end Greedy.InitialJournal

namespace Greedy.InitializedJoint

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open EntryJournal RestorationJournal

theorem exists_journal_history {n : ℕ} (initial comparator : BST 0 n) (H : ℕ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) (Execution.initial initial comparator (contractedGap H)) last requests)
    (bounded : execution.Bounded H) :
    let first := Execution.initial initial comparator (contractedGap H)
    let label := labels comparator (contractedGap H) first.blocks
    let state : WeightedMemory.State (External n) := ⟨label, label⟩
    ∃ actions : List (Action (External n)), ∃ history : LabelHistory.History (External n),
      LabelSnapshots.Sound last.comparator (contractedGap H) last.clock last.blocks history ∧
      LabelSnapshots.AllSourcesSnapshots history execution ∧ EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels last.comparator (contractedGap H) last.blocks ∧
      total ordinary state actions ≤ 2*n+1 + 11*execution.rotations ∧
      total internal state actions + total boundary state actions = execution.links ∧
      LabelHistory.variation history = total positiveChange state actions + total negativeChange state actions ∧
      CreatorPhase.shiftTotal execution ≤ 6*(total positiveChange state actions + total negativeChange state actions) ∧
      total positiveChange state actions ≤
        4*((contractedGap H : ℤ)-1)*(2*(2*n+1) + execution.births : ℕ) +
        22*((contractedGap H : ℤ)-1)*execution.rotations ∧
      total boundary state actions ≤ total negativeChange state actions +
        (2*(contractedGap H : ℤ)+4)*(2*(2*n+1) + execution.births : ℕ) ∧
      total good state actions ≤ total negativeChange state actions ∧
      total negativeEntry state actions ≤ 4*total negativeChange state actions +
        4*((contractedGap H : ℤ)-1)*(2*(2*n+1) + execution.births : ℕ) ∧
      total positiveEntry state actions ≤ total negativeChange state actions +
        13*((contractedGap H : ℤ)-1)*(2*(2*n+1) + execution.births : ℕ) ∧
      LiveMemory.Synced (run state actions).memory last.blocks ∧
      total shift state actions = LoserShift.sum execution ∧
      total creatorShift state actions = CreatorPhase.shiftTotal execution ∧
      total internal state actions ≤ 4*total deficit state actions + 4*total negativeChange state actions +
        total shift state actions + total creatorShift state actions + 4*(2*n+1) := by
  let first := Execution.initial initial comparator (contractedGap H)
  let label := labels comparator (contractedGap H) first.blocks
  let state : WeightedMemory.State (External n) := ⟨label, label⟩
  let old : LabelHistory.History (External n) := ⟨label, []⟩
  let entries := InitialJournal.program comparator first.refined.tree
  let entered := run state entries
  have initialValid := InitialJournal.install_valid
    (Splay.Lazy.Canonical.canonicalParent (Splay.Rank.Snapshot.ofTree comparator) first.refined.tree)
    Finset.univ.toList (contractedGap H) state
  have enteredLabel : entered.label = labels first.comparator (contractedGap H) first.blocks :=
    InitialJournal.program_labels comparator first.refined.tree state
  have oldSound : LabelSnapshots.Sound comparator (contractedGap H) first.clock first.blocks old :=
    LabelSnapshots.initial_sound comparator first.refined.tree (contractedGap H)
  have enteredMemory : LiveMemory.Synced entered.memory first.blocks :=
    LiveMemory.initial comparator first.refined.tree (contractedGap H) state rfl
  let initialPointer : External n → MembershipPointer.Ticket := fun _ => (0,0)
  let richEntries := TicketJournal.initial comparator first.refined.tree
  have richErase : WinnerCredit.erase richEntries = entries := TicketJournal.initial_erases ..
  have richAdmin : WinnerCredit.Administrative richEntries := TicketJournal.initial_administrative _ _
  have enteredPointer := TicketJournal.initial_pointer comparator first.refined.tree (contractedGap H)
    (⟨state, initialPointer⟩ : TicketJournal.State n)
  obtain ⟨tail, history, sound, _future, sources, tailValid, tailLabels, tailOrdinary, tailCount, tailVariation, tailPositive, tailBoundary, tailGood, tailNegativeEntry, tailPositiveEntry, finalMemory, tailShift, tailCreator, tailCertificate⟩ :=
    JointRunJournal.exists_joint H execution bounded (Execution.initial_valid initial comparator (contractedGap H))
      (GreedyMerge.GrowthBook.initial (Splay.Rank.Snapshot.ofTree comparator) first.refined.tree (contractedGap H))
      (GrowthJournal.initial_invariant (Splay.Rank.Snapshot.ofTree comparator) _ (contractedGap H))
      entered old enteredLabel oldSound enteredMemory (WinnerCredit.run ⟨state, initialPointer⟩ richEntries).ticket enteredPointer
  let actions := entries ++ tail
  have initialOrdinary : total ordinary state entries ≤ (2*n+1 : ℕ) := by
    have count := InitialJournal.install_count
      (Splay.Lazy.Canonical.canonicalParent (Splay.Rank.Snapshot.ofTree comparator) first.refined.tree) Finset.univ.toList state
    simpa only [entries, InitialJournal.program, Finset.length_toList, Finset.card_univ, Fintype.card_fin] using count
  have initialAbsolute : total absoluteChange state entries = 0 := InitialJournal.install_absolute_zero _ _ state
  have variation : LabelHistory.variation history = total positiveChange state actions + total negativeChange state actions := by
    rw [← total_absolute_eq, total_append, initialAbsolute, zero_add]
    simpa only [LabelHistory.variation, old, List.map_nil, List.sum_nil, zero_add] using tailVariation
  have kinds : OrdinaryOnly entries := InitialJournal.install_ordinary _ _
  refine ⟨actions, history, sound, sources, (valid_append ..).mpr ⟨initialValid, tailValid⟩, ?_, ?_, ?_, variation, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_append]; exact tailLabels
  · rw [total_append]
    push_cast at initialOrdinary
    linarith
  · rw [total_append, total_append, ordinaryOnly_internal_zero state entries kinds,
      ordinaryOnly_boundary_zero state entries kinds, zero_add, zero_add]
    exact tailCount
  · rw [← variation]
    exact CreatorPhase.initialized_shift_bound initial comparator (contractedGap H) execution history sources
  · have initialPositive : total positiveChange state entries = 0 := by
      have nonnegative : 0 ≤ total negativeChange state entries :=
        total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state entries
      have positiveNonnegative : 0 ≤ total positiveChange state entries :=
        total_nonneg positiveChange (fun current action => by cases action <;> simp [positiveChange, encode, WeightedMemory.positiveChange]) state entries
      rw [total_absolute_eq] at initialAbsolute
      omega
    have lifetime := DepartureAmounts.initialized_increase_bound initial comparator H execution bounded
    rw [total_append, initialPositive, zero_add]
    linarith
  · rw [total_append, ordinaryOnly_boundary_zero state entries kinds, zero_add, total_append]
    have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state entries
    have lifetime := DepartureAmounts.initialized_boundary_nondrop_bound initial comparator H execution bounded
    linarith
  · rw [total_append, ordinaryOnly_total_zero good (by intros; rfl) (by intros; rfl) state entries kinds, zero_add, total_append]
    have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state entries
    linarith
  · rw [total_append, ordinaryOnly_total_zero negativeEntry (by intros; rfl) (by intros; rfl) state entries kinds, zero_add, total_append]
    have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state entries
    have lifetime := IncomingExcess.initialized_mass_bound initial comparator H execution bounded
    linarith
  · rw [total_append, ordinaryOnly_total_zero positiveEntry (by intros; rfl) (by intros; rfl) state entries kinds, zero_add, total_append]
    have nonneg := total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state entries
    have lifetime := OutgoingExcess.initialized_combined_bound initial comparator H execution bounded
    linarith
  · rw [run_append]; exact finalMemory
  · rw [total_append, ordinaryOnly_total_zero shift (by intros; rfl) (by intros; rfl) state entries kinds, zero_add]
    exact tailShift
  · rw [total_append, ordinaryOnly_total_zero creatorShift (by intros; rfl) (by intros; rfl) state entries kinds, zero_add]
    exact tailCreator
  · have certificate := TicketJournal.certifies_append state initialPointer last.blocks entries tail
      (fun _ => 0) (fun ticket => WinnerTickets.total execution ticket.1 ticket.2)
      richEntries richErase (richAdmin.legal _) richAdmin.paired richAdmin.remaining_zero tailCertificate
    obtain ⟨annotated, erased, legal, paired, _synced, counts⟩ := certificate
    have capacity : ∀ ticket, WinnerCredit.remaining annotated ticket ≤ 4 := by
      intro ticket
      rw [counts]
      simpa only [Nat.zero_add] using WinnerTickets.initialized_total_le_four initial comparator (contractedGap H) execution ticket.1 ticket.2
    have bound := WinnerCredit.internal_bound label initialPointer annotated legal paired capacity
    rw [erased] at bound
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using bound

end Greedy.InitializedJoint
