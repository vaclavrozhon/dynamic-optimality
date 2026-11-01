import Greedy.TicketLinks

/-! The actual consolidation preserves membership pointers and validates every win observation. -/

namespace Greedy.TicketJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyMerge

theorem links_correct {n : ℕ}
    (parent : Parents n) (rank : ℕ → ℕ) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (time : ℕ) (states : States n)
    (events : List (External n × External n)) (roots finalRoots : List ℕ)
    (physical : Run rank (events.map eventKeys) roots finalRoots)
    (uniqueRoots : roots.Nodup)
    (rootParent : ∀ record : External n, record.val∈roots → parent record=some source)
    (notSource : ∀ record∈roots, record≠source.val)
    (sound : SoundFor parent states) (complete : CompleteFor parent states)
    (persistent : Persistent states)
    (emptySource : ∀ side, growerEntries (states source side).grower=[])
    (sideCorrect : ∀ event∈events, sourceSide event=decide (event.2.val<source.val))
    (orderedPrefixes : ∀ first second, events=first++second →
      Ordered (runLinks source sourceSide (fun _ current => GreedyMerge.StateLabels.label rank K current) time states first))
    (state : State n)
    (kind : External n × External n → EntryJournal.Kind)
    (oldTicket : External n → Ticket)
    (sourceTickets : ∀ record : External n, record.val ∈ roots → state.ticket record = oldTicket record)
    (agree : ∀ record, state.account.label record = GreedyMerge.StateLabels.label rank K states record.val)
    (synced : MembershipPointer.Synced state.ticket states) :
    WinnerCredit.Legal state (links rank K source sourceSide kind oldTicket time states events) ∧
    MembershipPointer.Synced (WinnerCredit.run state (links rank K source sourceSide kind oldTicket time states events)).ticket
      (runLinks source sourceSide (fun _ current => GreedyMerge.StateLabels.label rank K current) time states events) := by
  induction events generalizing parent states time roots state with
  | nil => exact ⟨trivial, synced⟩
  | cons event rest ih =>
      change Run rank (eventKeys event :: rest.map eventKeys) roots finalRoots at physical
      cases physical with
      | @cons _ _ _ middle _ firstLink restLinks =>
          have ordered : Ordered states := by
            simpa only [runLinks] using orderedPrefixes [] (event::rest) rfl
          have winnerNe : source≠event.1 := by
            intro same
            exact notSource event.1.val firstLink.members.1 (congrArg Fin.val same.symm)
          obtain ⟨oldSide,oldEntry,oldMember,oldKey⟩ :=
            complete event.2 source (rootParent event.2 firstLink.members.2)
          have oldSideEq : oldSide=sourceSide event := by
            rw [sideCorrect event (by simp)]
            have onCorrectSide := (ordered source oldSide).2.1 oldEntry oldMember
            unfold onSide at onCorrectSide
            rw [oldKey] at onCorrectSide
            cases oldSide with
            | false =>
                have less : source.val<event.2.val := onCorrectSide
                have notLess : ¬event.2.val<source.val := by omega
                simp only [notLess,decide_false]
            | true =>
                have less : event.2.val<source.val := onCorrectSide
                simp only [less,decide_true]
          rw [oldSideEq] at oldMember
          let fresh := arrivalEntry (GreedyMerge.StateLabels.label rank K states) event.1 event.2 time
          let next := linkState states source event.1 event.2 (sourceSide event) (targetSide event) fresh
          have nextSound : SoundFor (linkParents parent event.1 event.2) next :=
            linkState_sound parent states source event.1 event.2 (sourceSide event) (targetSide event)
              fresh sound ordered persistent winnerNe (emptySource _) oldEntry oldMember oldKey rfl
          have nextComplete : CompleteFor (linkParents parent event.1 event.2) next :=
            linkState_complete parent states source event.1 event.2 (sourceSide event) (targetSide event)
              fresh complete persistent (emptySource _) rfl
          have nextPersistent : Persistent next := linkState_persistent _ _ _ _ _ _ _ persistent
          have nextEmpty : ∀ side, growerEntries (next source side).grower=[] := by
            intro side
            dsimp only [next,linkState]
            simp only [winnerNe,false_and,↓reduceIte]
            split_ifs <;> exact emptySource side
          have nextRootParent : ∀ record : External n, record.val∈middle →
              linkParents parent event.1 event.2 record=some source := by
            intro record member
            have different : record≠event.2 := by
              intro same
              exact firstLink.loser_absent uniqueRoots (by simpa only [same,eventKeys] using member)
            rw [linkParents_other _ _ _ _ different]
            exact rootParent record (firstLink.sublist.subset member)
          have nextOrder : Ordered next := by
            simpa only [runLinks] using orderedPrefixes [event] rest rfl
          have oneLabel := StateLabels.linkState_label_of_next_sound
            (linkParents parent event.1 event.2) rank K states source event.1 event.2
            (sourceSide event) (targetSide event) fresh (persistent _ _) (emptySource _) rfl nextOrder nextSound
          let actions := pair rank (kind event) (oldTicket event.1) (receivingTicket states event time) event
          let nextState := WinnerCredit.run state actions
          obtain ⟨grower, present⟩ := Option.isSome_iff_exists.mp (persistent event.1 (targetSide event))
          have nextPointer : MembershipPointer.Synced nextState.ticket next := by
            rw [show nextState.ticket = Function.update state.ticket event.2 (receivingTicket states event time) from pair_ticket ..]
            simp only [receivingTicket, present, Option.map_some, Option.getD_some]
            exact MembershipPointer.link parent states source event.1 event.2 (sourceSide event) (targetSide event)
              fresh sound ordered winnerNe (emptySource _) oldEntry oldMember oldKey rfl grower present state.ticket synced
          have nextTickets : ∀ record : External n, record.val ∈ middle → nextState.ticket record = oldTicket record := by
            intro record member
            have different : record ≠ event.2 := by
              intro same
              exact firstLink.loser_absent uniqueRoots (by simpa only [same,eventKeys] using member)
            rw [show nextState.ticket = Function.update state.ticket event.2 (receivingTicket states event time) from pair_ticket ..,
              Function.update_of_ne different]
            exact sourceTickets record (firstLink.sublist.subset member)
          have nextAgree : ∀ record, nextState.account.label record =
              GreedyMerge.StateLabels.label rank K next record.val := by
            intro record
            rw [show nextState.account = AccessJournal.advance rank kind state.account event from pair_account .., AccessJournal.advance_labels rank kind (GreedyMerge.StateLabels.label rank K states) state.account event agree]
            exact (congrFun oneLabel record.val).symm
          have tail := ih (linkParents parent event.1 event.2) (time+1) next middle restLinks
            (uniqueRoots.sublist firstLink.sublist) nextRootParent
            (fun record member => notSource record (firstLink.sublist.subset member))
            nextSound nextComplete nextPersistent nextEmpty
            (fun e he => sideCorrect e (List.mem_cons_of_mem _ he))
            (by
              intro before after split
              have eq : event::rest=(event::before)++after := by simp [split]
              simpa only [runLinks] using orderedPrefixes (event::before) after eq)
            nextState nextTickets nextAgree nextPointer
          rw [links, WinnerCredit.legal_append, WinnerCredit.run_append]
          exact ⟨⟨pair_legal _ _ _ _ _ state (sourceTickets event.1 firstLink.members.1), tail.1⟩, tail.2⟩

end Greedy.TicketJournal
