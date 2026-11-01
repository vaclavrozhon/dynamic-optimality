import Splay.Accounting.MultiZigZigBoundaryPairingRealizer
import Splay.Accounting.ScheduleExecutionProvenance

namespace Splay.Accounting

open Splay.Assumptions.NormalForm
open Splay.Assumptions.NormalForm.ComparisonTrace
open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

namespace RepresentedShiftAtomicPreparation

/--
Shift-atomic preparation packaged as a represented identity transition.

The preparation preserves the exact heap view, so the represented snapshot
and splay tree are unchanged.  This is the bridge from an arbitrary
comparison-rotation endpoint to the input required by the concrete boundary
macro.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : BST 0 n}
    (initial : State n) where
  transition :
    RepresentedTransition params
      snapshot tree snapshot tree initial
  finalAtomic : transition.final.ShiftAtomic

theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {tree : BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot tree) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        (tree := tree) initial) := by
  obtain ⟨preparation⟩ :=
    Splay.Lazy.existsShiftAtomicPreparation
      initial initialRepresents.stable
  have finalHeapOrdered :
      preparation.final.view.HeapOrdered := by
    rw [preparation.view_eq]
    exact initialRepresents.heapOrdered
  have finalStable : preparation.final.Stable params :=
    preparation.rankPrepared.stable finalHeapOrdered
  have finalRepresents :
      preparation.final.Represents params snapshot tree :=
    ⟨finalStable,
      preparation.view_eq.trans initialRepresents.view_eq⟩
  let transition :
      RepresentedTransition params
        snapshot tree snapshot tree initial := {
    initial_represents := initialRepresents
    final := preparation.final
    events := preparation.events
    trace := preparation.trace
    final_represents := finalRepresents
  }
  exact
    ⟨{
      transition := transition
      finalAtomic := preparation.shiftAtomic
    }⟩

end RepresentedShiftAtomicPreparation

namespace ComparisonTrace.Schedule

/--
The genuine splay transcripts chosen at every request group of a schedule.

Comparison-only segments contribute no splay kind.  At a `next` node, the
kind list is exactly the current group's dependent splay-sequence transcript
followed by the tail schedule's kind list.
-/
inductive BoundaryPairingTranscript
    {n : ℕ} {accesses : List (Fin n)}
    {comparison : ComparisonTrace n accesses} :
    {groups : List (RequestGroup comparison)} →
    {time : Fin (comparison.rotationCount + 1)} →
    {beforeTree afterTree : BST 0 n} →
    (schedule :
      Schedule comparison groups time beforeTree afterTree) →
    List SplayStepKind → Prop
  | finish
      {finishTime : Fin (comparison.rotationCount + 1)}
      (tree : BST 0 n)
      (rotations :
        RotationExecution
          (comparison.rotationCount - finishTime.val)
          (comparison.state finishTime) comparison.finalTree) :
      BoundaryPairingTranscript
        (.finish tree rotations) []
  | next
      {group : RequestGroup comparison}
      {tailGroups : List (RequestGroup comparison)}
      {startTime : Fin (comparison.rotationCount + 1)}
      {before middle after : BST 0 n}
      (ordered : startTime ≤ group.time)
      (rotations :
        RotationExecution
          (group.time.val - startTime.val)
          (comparison.state startTime)
          (comparison.state group.time))
      (splay : SplaySequence group.requests before middle)
      (tail :
        Schedule comparison tailGroups group.time middle after)
      {headKinds : List SplayStepKind}
      {headZig headZigZig headZigZag : ℕ}
      (headTranscript :
        SplaySequenceTranscript splay headKinds
          headZig headZigZig headZigZag)
      {tailKinds : List SplayStepKind}
      (tailTranscript :
        BoundaryPairingTranscript tail tailKinds) :
      BoundaryPairingTranscript
        (.next ordered rotations splay tail)
        (headKinds ++ tailKinds)

/--
An exact normal-form schedule realization that executes the concrete
two-boundary macro at every zig-zig in every request group.

`firstMoves` and `secondMoves` live in the one global rich trace.  Their slot
indices are globally offset across request groups, while
`splayTranscript` proves that the accumulated kind list comes from the actual
dependent splay sequences stored in this exact schedule.
-/
structure BoundaryPairingCertificate
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {comparison : ComparisonTrace n accesses}
    {groups : List (RequestGroup comparison)}
    {time : Fin (comparison.rotationCount + 1)}
    {beforeTree afterTree : BST 0 n}
    (schedule :
      Schedule comparison groups time beforeTree afterTree)
    (initial : State n) (start : ℕ) where
  transition :
    RepresentedTransition params
      (Snapshot.ofTree (comparison.state time)) beforeTree
      (Snapshot.ofTree comparison.finalTree) afterTree initial
  kinds : List SplayStepKind
  splayTranscript : BoundaryPairingTranscript schedule kinds
  firstMoves : List (BoundaryPairingMove transition.trace)
  secondMoves : List (BoundaryPairingMove transition.trace)
  firstSlots_eq :
    firstMoves.map BoundaryPairingMove.slot =
      firstPairingsFrom start kinds
  secondSlots_eq :
    secondMoves.map BoundaryPairingMove.slot =
      secondPairingsFrom start kinds

/--
Every normal-form schedule has a concrete boundary-pairing realization from
an arbitrary shift-atomic represented state.

At each `next` node the construction performs, in order:

1. the exact comparison-rotation transition;
2. historical shift-atomic preparation at the new comparison snapshot;
3. the full multi-request boundary macro for the current request group; and
4. the recursively realized tail schedule.
-/
theorem exists_boundaryPairingCertificate
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {comparison : ComparisonTrace n accesses}
    {groups : List (RequestGroup comparison)}
    {time : Fin (comparison.rotationCount + 1)}
    {beforeTree afterTree : BST 0 n}
    (schedule :
      Schedule comparison groups time beforeTree afterTree)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree (comparison.state time)) beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (start : ℕ) :
    Nonempty
      (BoundaryPairingCertificate
        (params := params) schedule initial start) := by
  induction schedule generalizing initial start with
  | @finish finishTime tree rotations =>
      obtain ⟨⟨transition, _provenance⟩⟩ :=
        RotationExecution.RepresentedComparisonTransitionProvenance.exists_complete
          rotations initialRepresents
      exact
        ⟨{
          transition := transition
          kinds := []
          splayTranscript := .finish tree rotations
          firstMoves := []
          secondMoves := []
          firstSlots_eq := by simp [firstPairingsFrom]
          secondSlots_eq := by simp [secondPairingsFrom]
        }⟩
  | @next group tailGroups startTime before middle after
      ordered rotations splay tail ih =>
      obtain ⟨⟨comparisonTransition, _comparisonProvenance⟩⟩ :=
        RotationExecution.RepresentedComparisonTransitionProvenance.exists_complete
          rotations initialRepresents
      obtain ⟨preparation⟩ :=
        RepresentedShiftAtomicPreparation.exists_certificate
          comparisonTransition.final_represents
      let prefixTransition :=
        comparisonTransition.trans preparation.transition
      let headWitness := splaySequenceTranscriptWitness splay
      obtain ⟨headCertificate⟩ :=
        SplaySequenceBoundaryPairingMacro.exists_certificate
          headWitness.transcript
          preparation.transition.final_represents
          preparation.finalAtomic start
      obtain ⟨tailCertificate⟩ :=
        ih headCertificate.transition.final_represents
          headCertificate.finalAtomic
          (start + headWitness.kinds.length)
      let splayAndTail :=
        headCertificate.transition.trans tailCertificate.transition
      let transition :=
        prefixTransition.trans splayAndTail
      let rawHeadFirst :=
        BoundaryPairingMove.prependAll
          (BoundaryPairingMove.appendAll
            headCertificate.firstMoves tailCertificate.transition.trace)
          prefixTransition.trace
      let rawTailFirst :=
        BoundaryPairingMove.prependAll
          (BoundaryPairingMove.prependAll
            tailCertificate.firstMoves headCertificate.transition.trace)
          prefixTransition.trace
      let rawHeadSecond :=
        BoundaryPairingMove.prependAll
          (BoundaryPairingMove.appendAll
            headCertificate.secondMoves tailCertificate.transition.trace)
          prefixTransition.trace
      let rawTailSecond :=
        BoundaryPairingMove.prependAll
          (BoundaryPairingMove.prependAll
            tailCertificate.secondMoves headCertificate.transition.trace)
          prefixTransition.trace
      let rawFirstMoves := rawHeadFirst ++ rawTailFirst
      let rawSecondMoves := rawHeadSecond ++ rawTailSecond
      let firstMoves :=
        BoundaryPairingMove.castAll transition.trace rawFirstMoves
      let secondMoves :=
        BoundaryPairingMove.castAll transition.trace rawSecondMoves
      have firstMovesSlots :
          firstMoves.map BoundaryPairingMove.slot =
            headCertificate.firstMoves.map BoundaryPairingMove.slot ++
              tailCertificate.firstMoves.map
                BoundaryPairingMove.slot := by
        calc
          firstMoves.map BoundaryPairingMove.slot =
              rawFirstMoves.map BoundaryPairingMove.slot := by
            exact
              BoundaryPairingMove.castAll_slots
                transition.trace rawFirstMoves
          _ = headCertificate.firstMoves.map
                  BoundaryPairingMove.slot ++
                tailCertificate.firstMoves.map
                  BoundaryPairingMove.slot := by
            simp [rawFirstMoves, rawHeadFirst, rawTailFirst]
      have secondMovesSlots :
          secondMoves.map BoundaryPairingMove.slot =
            headCertificate.secondMoves.map BoundaryPairingMove.slot ++
              tailCertificate.secondMoves.map
                BoundaryPairingMove.slot := by
        calc
          secondMoves.map BoundaryPairingMove.slot =
              rawSecondMoves.map BoundaryPairingMove.slot := by
            exact
              BoundaryPairingMove.castAll_slots
                transition.trace rawSecondMoves
          _ = headCertificate.secondMoves.map
                  BoundaryPairingMove.slot ++
                tailCertificate.secondMoves.map
                  BoundaryPairingMove.slot := by
            simp [rawSecondMoves, rawHeadSecond, rawTailSecond]
      exact
        ⟨{
          transition := transition
          kinds := headWitness.kinds ++ tailCertificate.kinds
          splayTranscript :=
            .next ordered rotations splay tail
              headWitness.transcript tailCertificate.splayTranscript
          firstMoves := firstMoves
          secondMoves := secondMoves
          firstSlots_eq := by
            calc
              firstMoves.map BoundaryPairingMove.slot =
                  headCertificate.firstMoves.map
                      BoundaryPairingMove.slot ++
                    tailCertificate.firstMoves.map
                      BoundaryPairingMove.slot :=
                firstMovesSlots
              _ = firstPairingsFrom start headWitness.kinds ++
                    firstPairingsFrom
                      (start + headWitness.kinds.length)
                      tailCertificate.kinds := by
                rw [headCertificate.firstSlots_eq,
                  tailCertificate.firstSlots_eq]
              _ = firstPairingsFrom start
                    (headWitness.kinds ++ tailCertificate.kinds) := by
                rw [firstPairingsFrom_append]
          secondSlots_eq := by
            calc
              secondMoves.map BoundaryPairingMove.slot =
                  headCertificate.secondMoves.map
                      BoundaryPairingMove.slot ++
                    tailCertificate.secondMoves.map
                      BoundaryPairingMove.slot :=
                secondMovesSlots
              _ = secondPairingsFrom start headWitness.kinds ++
                    secondPairingsFrom
                      (start + headWitness.kinds.length)
                      tailCertificate.kinds := by
                rw [headCertificate.secondSlots_eq,
                  tailCertificate.secondSlots_eq]
              _ = secondPairingsFrom start
                    (headWitness.kinds ++ tailCertificate.kinds) := by
                rw [secondPairingsFrom_append]
        }⟩

/--
The initialized schedule package retains the exact boundary-pairing suffix
next to the initialization that supplies its initial state.

Unlike a pair of unrelated existence statements, this dependent package
makes it definitionally clear that `suffix.transition` is the represented
suffix of `execution`.
-/
structure InitializedBoundaryPairingCertificate
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {comparison : ComparisonTrace n accesses}
    {groups : List (RequestGroup comparison)}
    {time : Fin (comparison.rotationCount + 1)}
    {beforeTree afterTree : BST 0 n}
    (schedule :
      Schedule comparison groups time beforeTree afterTree)
    (initialization :
      Initialization params
        (Snapshot.ofTree (comparison.state time)) beforeTree) where
  suffix :
    BoundaryPairingCertificate
      (params := params) schedule initialization.final 0

namespace InitializedBoundaryPairingCertificate

/-- Forget the pairing fields while retaining the very same initialized run. -/
def execution
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {comparison : ComparisonTrace n accesses}
    {groups : List (RequestGroup comparison)}
    {time : Fin (comparison.rotationCount + 1)}
    {beforeTree afterTree : BST 0 n}
    {schedule :
      Schedule comparison groups time beforeTree afterTree}
    {initialization :
      Initialization params
        (Snapshot.ofTree (comparison.state time)) beforeTree}
    (certificate :
      InitializedBoundaryPairingCertificate schedule initialization) :
    InitializedTransition params
      (Snapshot.ofTree (comparison.state time)) beforeTree
      (Snapshot.ofTree comparison.finalTree) afterTree where
  initialization := initialization
  transition := certificate.suffix.transition

end InitializedBoundaryPairingCertificate

/--
Atomic initialization produces a dependently linked complete schedule
certificate: its initialized execution and every exported pairing move share
the exact same represented suffix.
-/
theorem exists_atomicInitialized_linkedBoundaryPairingCertificate
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {comparison : ComparisonTrace n accesses}
    {groups : List (RequestGroup comparison)}
    {time : Fin (comparison.rotationCount + 1)}
    {beforeTree afterTree : BST 0 n}
    (schedule :
      Schedule comparison groups time beforeTree afterTree)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree (comparison.state time)).maxRank ≤
        params.valueBound) :
    let initialization :=
      Splay.Lazy.Canonical.atomicInitialization
        (Snapshot.ofTree (comparison.state time)) beforeTree
        params growingLimit valueBound
    Nonempty
      (InitializedBoundaryPairingCertificate
        (params := params) schedule initialization) := by
  let initialization :=
    Splay.Lazy.Canonical.atomicInitialization
      (Snapshot.ofTree (comparison.state time)) beforeTree
      params growingLimit valueBound
  have initialAtomic : initialization.final.ShiftAtomic :=
    atomicInitialization_final_shiftAtomic
      (Snapshot.ofTree (comparison.state time)) beforeTree
      params growingLimit valueBound
  obtain ⟨suffix⟩ :=
    exists_boundaryPairingCertificate schedule
      initialization.final_represents initialAtomic 0
  exact ⟨{ suffix := suffix }⟩

/--
Atomic initialization supplies the input of the complete schedule boundary
realizer.  The result is one initialized execution whose represented suffix
contains both moves of every genuine schedule zig-zig.
-/
theorem exists_atomicInitialized_boundaryPairingCertificate
    {n : ℕ} {accesses : List (Fin n)}
    {params : Interface.Parameters}
    {comparison : ComparisonTrace n accesses}
    {groups : List (RequestGroup comparison)}
    {time : Fin (comparison.rotationCount + 1)}
    {beforeTree afterTree : BST 0 n}
    (schedule :
      Schedule comparison groups time beforeTree afterTree)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap
          (Snapshot.ofTree (comparison.state time)).maxRank ≤
        params.valueBound) :
    let initialization :=
      Splay.Lazy.Canonical.atomicInitialization
        (Snapshot.ofTree (comparison.state time)) beforeTree
        params growingLimit valueBound
    Nonempty
      (InitializedBoundaryPairingCertificate
        (params := params) schedule initialization) :=
  exists_atomicInitialized_linkedBoundaryPairingCertificate
    schedule growingLimit valueBound

end ComparisonTrace.Schedule

end Splay.Accounting
