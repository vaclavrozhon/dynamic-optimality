import Splay.Accounting.BoundaryPairingMoveComposition
import Splay.Accounting.RequestStartBoundaryLineage

namespace Splay.Accounting

open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

namespace HeapChildPairing

/-- The two phase choices remove different ternary branches. -/
theorem loserBranch_first_ne_second
    (heavy : TernaryBranch) :
    loserBranch heavy .first ≠ loserBranch heavy .second := by
  cases heavy <;> decide

/-- Consequently the two canonical phase losers at one node are distinct. -/
theorem ofNode_losers_ne
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (ofNode snapshot node .first).loser ≠
      (ofNode snapshot node .second).loser := by
  intro equal
  have branchEqual :
      loserBranch (node.heavyBranch snapshot) .first =
        loserBranch (node.heavyBranch snapshot) .second :=
    (branchMin_injective snapshot node) equal
  exact
    loserBranch_first_ne_second
      (node.heavyBranch snapshot) branchEqual

end HeapChildPairing

namespace ZigZigPairingEndpointsAt

/--
Extract both endpoint phases at once.  Unlike two unrelated applications of
`exists_of_orientation`, the joint witness also retains the fact that the two
losers are distinct.
-/
theorem exists_both_of_orientation
    {n : ℕ} (snapshot : Snapshot n)
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key) before after)
    (upper_le_n : upper ≤ n) :
    ∃ firstWinner firstLoser secondWinner secondLoser,
      ZigZigPairingEndpointsAt snapshot .first
          (depth := depth) (key := key)
          before after firstWinner firstLoser ∧
        ZigZigPairingEndpointsAt snapshot .second
          (depth := depth) (key := key)
          before after secondWinner secondLoser ∧
        firstLoser ≠ secondLoser := by
  generalize flag_eq : true = flag at orientation
  induction orientation with
  | @zigZigLeft lower first second third upper a b c d =>
      let node : AtNode n := {
        lower := second + 1
        root := third
        upper := upper
        left := c
        right := d
        upper_le_n := upper_le_n
      }
      exact
        ⟨(HeapChildPairing.ofNode snapshot node .first).winner,
          (HeapChildPairing.ofNode snapshot node .first).loser,
          (HeapChildPairing.ofNode snapshot node .second).winner,
          (HeapChildPairing.ofNode snapshot node .second).loser,
          .zigZigLeft a b c d upper_le_n .first,
          .zigZigLeft a b c d upper_le_n .second,
          HeapChildPairing.ofNode_losers_ne snapshot node⟩
  | @zigZigRight lower first second third upper a b c d =>
      have second_le_n : second ≤ n := by
        have cBounds := c.lower_le_upper
        have dBounds := d.lower_le_upper
        omega
      let node : AtNode n := {
        lower := lower
        root := first
        upper := second
        left := a
        right := b
        upper_le_n := second_le_n
      }
      exact
        ⟨(HeapChildPairing.ofNode snapshot node .first).winner,
          (HeapChildPairing.ofNode snapshot node .first).loser,
          (HeapChildPairing.ofNode snapshot node .second).winner,
          (HeapChildPairing.ofNode snapshot node .second).loser,
          .zigZigRight a b c d upper_le_n second_le_n .first,
          .zigZigRight a b c d upper_le_n second_le_n .second,
          HeapChildPairing.ofNode_losers_ne snapshot node⟩
  | zigZagLeftRight =>
      contradiction
  | zigZagRightLeft =>
      contradiction
  | leftContext orientation right ih =>
      obtain
          ⟨firstWinner, firstLoser, secondWinner, secondLoser,
            firstEndpoints, secondEndpoints, losersNe⟩ :=
        ih (by
          have rightBounds := right.lower_le_upper
          omega) flag_eq
      exact
        ⟨firstWinner, firstLoser, secondWinner, secondLoser,
          .leftContext firstEndpoints right,
          .leftContext secondEndpoints right, losersNe⟩
  | rightContext left orientation ih =>
      obtain
          ⟨firstWinner, firstLoser, secondWinner, secondLoser,
            firstEndpoints, secondEndpoints, losersNe⟩ :=
        ih upper_le_n flag_eq
      exact
        ⟨firstWinner, firstLoser, secondWinner, secondLoser,
          .rightContext left firstEndpoints,
          .rightContext left secondEndpoints, losersNe⟩

end ZigZigPairingEndpointsAt

namespace ZigZigBoundaryPairingMacro

/--
Two concrete boundary moves implementing the two heap-child pairings attached
to one genuine zig-zig.

The first represented transition changes the canonical tree from `beforeTree`
to `afterTree`.  Its final state is again shift atomic, so the second pairing
can be performed as an `afterTree`-to-`afterTree` represented transition.
Both moves are then transported to the single concatenated rich trace.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {depth key : ℕ}
    (initial : State n) (zigZigStep : ℕ)
    (firstWinner firstLoser secondWinner secondLoser : Interface.Element n)
    where
  firstEndpoints :
    ZigZigPairingEndpointsAt snapshot .first
      (depth := depth) (key := key)
      beforeTree afterTree firstWinner firstLoser
  secondEndpoints :
    ZigZigPairingEndpointsAt snapshot .second
      (depth := depth) (key := key)
      beforeTree afterTree secondWinner secondLoser
  losers_ne : firstLoser ≠ secondLoser
  initialAtomic : initial.ShiftAtomic
  firstTransition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  firstFinalAtomic : firstTransition.final.ShiftAtomic
  secondTransition :
    RepresentedTransition params
      snapshot afterTree snapshot afterTree firstTransition.final
  secondLoser_no_leave_in_first :
    ∀ operation,
      operation ∈ eraseOperations firstTransition.events →
        ¬operationLeavesElement operation secondLoser
  finalAtomic : secondTransition.final.ShiftAtomic
  firstMove :
    BoundaryPairingMove
      (firstTransition.trans secondTransition).trace
  secondMove :
    BoundaryPairingMove
      (firstTransition.trans secondTransition).trace
  first_slot :
    firstMove.slot =
      { zigZigStep := zigZigStep, phase := .first }
  second_slot :
    secondMove.slot =
      { zigZigStep := zigZigStep, phase := .second }
  first_winner : firstMove.winner = firstWinner
  first_loser : firstMove.loser = firstLoser
  second_winner : secondMove.winner = secondWinner
  second_loser : secondMove.loser = secondLoser
  first_events_eq :
    firstTransition.events =
      [.operation (.delete firstMove.source firstLoser),
        .silent,
        .operation (.valueChange firstLoser .increase),
        .operation (.insert firstMove.destination firstLoser),
        .operation (.valueChange firstLoser .decrease),
        .operation (.convert firstMove.destination),
        .operation (.create firstMove.destinationBlock.creator)]
  second_events_eq :
    secondTransition.events =
      [.operation (.delete secondMove.source secondLoser),
        .silent,
        .operation (.valueChange secondLoser .increase),
        .operation (.insert secondMove.destination secondLoser),
        .operation (.valueChange secondLoser .decrease),
        .operation (.convert secondMove.destination),
        .operation (.create secondMove.destinationBlock.creator)]
  first_delete_event_index : firstMove.deleteEventIndex = 0
  first_insert_event_index : firstMove.insertEventIndex = 3
  second_delete_event_index :
    secondMove.deleteEventIndex = firstTransition.events.length
  second_insert_event_index :
    secondMove.insertEventIndex = firstTransition.events.length + 3
  first_delete_operation_index :
    firstMove.deleteOperationIndex = 0
  first_insert_operation_index :
    firstMove.insertOperationIndex = 2
  second_delete_operation_index :
    secondMove.deleteOperationIndex =
      (eraseOperations firstTransition.events).length
  second_insert_operation_index :
    secondMove.insertOperationIndex =
      (eraseOperations firstTransition.events).length + 2
  first_insert_before_second_delete :
    firstMove.insertEventIndex < secondMove.deleteEventIndex

/-- The single represented transition executed by a two-pair certificate. -/
def Certificate.transition
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {depth key : ℕ}
    {initial : State n} {zigZigStep : ℕ}
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (certificate :
      Certificate (params := params) (snapshot := snapshot)
        (beforeTree := beforeTree) (afterTree := afterTree)
        (depth := depth) (key := key)
        initial zigZigStep
        firstWinner firstLoser secondWinner secondLoser) :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial :=
  certificate.firstTransition.trans certificate.secondTransition

/--
Inside the macro trace itself, the second loser has not left before its own
delete.  A caller embedding the macro later in a request need only discharge
the additional request-prefix part.
-/
theorem Certificate.secondLoser_no_prior_leave
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {depth key : ℕ}
    {initial : State n} {zigZigStep : ℕ}
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (certificate :
      Certificate (params := params) (snapshot := snapshot)
        (beforeTree := beforeTree) (afterTree := afterTree)
        (depth := depth) (key := key)
        initial zigZigStep
        firstWinner firstLoser secondWinner secondLoser) :
    ∀ prior,
      prior ∈
          (eraseOperations certificate.transition.events).take
            certificate.secondMove.deleteOperationIndex →
        ¬operationLeavesElement prior secondLoser := by
  intro prior member
  apply certificate.secondLoser_no_leave_in_first prior
  change
    prior ∈
      (eraseOperations
        (certificate.firstTransition.events ++
          certificate.secondTransition.events)).take
        certificate.secondMove.deleteOperationIndex at member
  rw [certificate.second_delete_operation_index,
    eraseOperations_append, List.take_append] at member
  simpa using member

/--
Concrete construction from the two canonical endpoint witnesses of a zig-zig.

No event occurrence is postulated: both delete/insert pairs are constructed by
`ShiftAtomicBoundaryPairing.exists_certificate`, and the transport lemmas place
them at their exact positions in the concatenated trace.
-/
theorem exists_certificate_of_endpoints
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {depth key : ℕ}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (zigZigStep : ℕ)
    {firstWinner firstLoser secondWinner secondLoser :
      Interface.Element n}
    (firstEndpoints :
      ZigZigPairingEndpointsAt snapshot .first
        (depth := depth) (key := key)
        beforeTree afterTree firstWinner firstLoser)
    (secondEndpoints :
      ZigZigPairingEndpointsAt snapshot .second
        (depth := depth) (key := key)
        beforeTree afterTree secondWinner secondLoser)
    (losersNe : firstLoser ≠ secondLoser) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        (beforeTree := beforeTree) (afterTree := afterTree)
        (depth := depth) (key := key)
        initial zigZigStep
        firstWinner firstLoser secondWinner secondLoser) := by
  let firstSlot : PairingSlot :=
    { zigZigStep := zigZigStep, phase := .first }
  let secondSlot : PairingSlot :=
    { zigZigStep := zigZigStep, phase := .second }
  obtain ⟨firstCertificate⟩ :=
    ShiftAtomicBoundaryPairing.exists_certificate
      initialRepresents initialAtomic firstSlot
      firstWinner firstLoser firstEndpoints.after_canonicalParent
  obtain ⟨secondCertificate⟩ :=
    ShiftAtomicBoundaryPairing.exists_certificate
      firstCertificate.transition.final_represents
      firstCertificate.finalAtomic secondSlot
      secondWinner secondLoser secondEndpoints.after_canonicalParent
  let firstMove :=
    firstCertificate.move.append secondCertificate.transition.trace
  let secondMove :=
    secondCertificate.move.prepend firstCertificate.transition.trace
  have firstInsertInside :
      firstCertificate.move.insertEventIndex <
        firstCertificate.transition.events.length :=
    firstCertificate.move.insertAt.eventIndex_lt
  have firstBeforeSecond :
      firstMove.insertEventIndex < secondMove.deleteEventIndex := by
    change
      firstCertificate.move.insertEventIndex <
        firstCertificate.transition.events.length +
          secondCertificate.move.deleteEventIndex
    rw [secondCertificate.delete_event_index, Nat.add_zero]
    exact firstInsertInside
  have secondNoLeaveInFirst :
      ∀ operation,
        operation ∈
            eraseOperations firstCertificate.transition.events →
          ¬operationLeavesElement operation secondLoser := by
    intro operation member
    rw [firstCertificate.events_eq] at member
    simp [eraseOperations, Event.operations] at member
    rcases member with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [operationLeavesElement, losersNe]
  exact
    ⟨{
      firstEndpoints := firstEndpoints
      secondEndpoints := secondEndpoints
      losers_ne := losersNe
      initialAtomic := initialAtomic
      firstTransition := firstCertificate.transition
      firstFinalAtomic := firstCertificate.finalAtomic
      secondTransition := secondCertificate.transition
      secondLoser_no_leave_in_first := secondNoLeaveInFirst
      finalAtomic := secondCertificate.finalAtomic
      firstMove := firstMove
      secondMove := secondMove
      first_slot := by
        exact firstCertificate.move_slot
      second_slot := by
        exact secondCertificate.move_slot
      first_winner := by
        exact firstCertificate.move_winner
      first_loser := by
        exact firstCertificate.move_loser
      second_winner := by
        exact secondCertificate.move_winner
      second_loser := by
        exact secondCertificate.move_loser
      first_events_eq := by
        exact firstCertificate.events_eq
      second_events_eq := by
        exact secondCertificate.events_eq
      first_delete_event_index := by
        exact firstCertificate.delete_event_index
      first_insert_event_index := by
        exact firstCertificate.insert_event_index
      second_delete_event_index := by
        change
          firstCertificate.transition.events.length +
              secondCertificate.move.deleteEventIndex =
            firstCertificate.transition.events.length
        rw [secondCertificate.delete_event_index, Nat.add_zero]
      second_insert_event_index := by
        change
          firstCertificate.transition.events.length +
              secondCertificate.move.insertEventIndex =
            firstCertificate.transition.events.length + 3
        rw [secondCertificate.insert_event_index]
      first_delete_operation_index := by
        exact firstCertificate.delete_operation_index
      first_insert_operation_index := by
        exact firstCertificate.insert_operation_index
      second_delete_operation_index := by
        change
          (eraseOperations firstCertificate.transition.events).length +
              secondCertificate.move.deleteOperationIndex =
            (eraseOperations firstCertificate.transition.events).length
        rw [secondCertificate.delete_operation_index, Nat.add_zero]
      second_insert_operation_index := by
        change
          (eraseOperations firstCertificate.transition.events).length +
              secondCertificate.move.insertOperationIndex =
            (eraseOperations firstCertificate.transition.events).length + 2
        rw [secondCertificate.insert_operation_index]
      first_insert_before_second_delete := firstBeforeSecond
    }⟩

/--
Every concrete true double-orientation at the root admits the complete
two-boundary-pairing macro, with the phase slots tied to `zigZigStep`.
-/
theorem exists_certificate_of_orientation
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {depth key : ℕ}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (zigZigStep : ℕ)
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key)
        beforeTree afterTree) :
    ∃ firstWinner firstLoser secondWinner secondLoser,
      Nonempty
        (Certificate (params := params) (snapshot := snapshot)
          (beforeTree := beforeTree) (afterTree := afterTree)
          (depth := depth) (key := key)
          initial zigZigStep
          firstWinner firstLoser secondWinner secondLoser) := by
  obtain
      ⟨firstWinner, firstLoser, secondWinner, secondLoser,
        firstEndpoints, secondEndpoints, losersNe⟩ :=
    ZigZigPairingEndpointsAt.exists_both_of_orientation
      snapshot orientation (Nat.le_refl n)
  exact
    ⟨firstWinner, firstLoser, secondWinner, secondLoser,
      exists_certificate_of_endpoints
        initialRepresents initialAtomic zigZigStep
        firstEndpoints secondEndpoints losersNe⟩

end ZigZigBoundaryPairingMacro

end Splay.Accounting
