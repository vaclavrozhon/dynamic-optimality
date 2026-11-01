import Splay.Accounting.InitializedCostSensitivePairingAlignment
import Splay.Lazy.AtomicRealizersComplete

namespace Splay.Accounting

open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

/-- First-phase pairing slots whose chronological indices start at `start`. -/
def firstPairingsFrom
    (start : ℕ) (kinds : List SplayStepKind) : List PairingSlot :=
  (kinds.findIdxs SplayStepKind.isZigZig start).map fun step =>
    { zigZigStep := step, phase := .first }

/-- Second-phase pairing slots whose chronological indices start at `start`. -/
def secondPairingsFrom
    (start : ℕ) (kinds : List SplayStepKind) : List PairingSlot :=
  (kinds.findIdxs SplayStepKind.isZigZig start).map fun step =>
    { zigZigStep := step, phase := .second }

@[simp]
theorem firstPairingsFrom_zero (kinds : List SplayStepKind) :
    firstPairingsFrom 0 kinds = firstPairings kinds :=
  rfl

@[simp]
theorem secondPairingsFrom_zero (kinds : List SplayStepKind) :
    secondPairingsFrom 0 kinds = secondPairings kinds :=
  rfl

theorem firstPairingsFrom_append
    (start : ℕ) (left right : List SplayStepKind) :
    firstPairingsFrom start (left ++ right) =
      firstPairingsFrom start left ++
        firstPairingsFrom (start + left.length) right := by
  simp [firstPairingsFrom, List.findIdxs_append, List.map_append]

theorem secondPairingsFrom_append
    (start : ℕ) (left right : List SplayStepKind) :
    secondPairingsFrom start (left ++ right) =
      secondPairingsFrom start left ++
        secondPairingsFrom (start + left.length) right := by
  simp [secondPairingsFrom, List.findIdxs_append, List.map_append]

namespace BoundaryPairingMove

/-- Reindex a move along proof irrelevance of two proofs of the same trace. -/
def castTrace
    {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {sourceTrace : Trace params initial events final}
    (targetTrace : Trace params initial events final)
    (move : BoundaryPairingMove sourceTrace) :
    BoundaryPairingMove targetTrace := by
  have traceEq : sourceTrace = targetTrace := Subsingleton.elim _ _
  cases traceEq
  exact move

/-- Reindex a list of moves along proof irrelevance of the trace proof. -/
def castAll
    {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {sourceTrace : Trace params initial events final}
    (targetTrace : Trace params initial events final)
    (moves : List (BoundaryPairingMove sourceTrace)) :
    List (BoundaryPairingMove targetTrace) :=
  moves.map fun move => move.castTrace targetTrace

@[simp]
theorem castTrace_slot
    {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {sourceTrace : Trace params initial events final}
    (targetTrace : Trace params initial events final)
    (move : BoundaryPairingMove sourceTrace) :
    (move.castTrace targetTrace).slot = move.slot := by
  have traceEq : sourceTrace = targetTrace := Subsingleton.elim _ _
  cases traceEq
  rfl

@[simp]
theorem castAll_slots
    {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {sourceTrace : Trace params initial events final}
    (targetTrace : Trace params initial events final)
    (moves : List (BoundaryPairingMove sourceTrace)) :
    (castAll targetTrace moves).map BoundaryPairingMove.slot =
      moves.map BoundaryPairingMove.slot := by
  have traceEq : sourceTrace = targetTrace := Subsingleton.elim _ _
  cases traceEq
  simp [castAll, castTrace]

/-- Transport every move in a trace prefix through one common suffix. -/
def appendAll
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (moves : List (BoundaryPairingMove prefixTrace))
    (suffixTrace : Trace params middle suffixEvents final) :
    List (BoundaryPairingMove (prefixTrace.append suffixTrace)) :=
  moves.map fun move => move.append suffixTrace

/-- Transport every move in a trace suffix through one common prefix. -/
def prependAll
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {suffixTrace : Trace params middle suffixEvents final}
    (moves : List (BoundaryPairingMove suffixTrace))
    (prefixTrace : Trace params initial prefixEvents middle) :
    List (BoundaryPairingMove (prefixTrace.append suffixTrace)) :=
  moves.map fun move => move.prepend prefixTrace

@[simp]
theorem appendAll_slots
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (moves : List (BoundaryPairingMove prefixTrace))
    (suffixTrace : Trace params middle suffixEvents final) :
    (BoundaryPairingMove.appendAll moves suffixTrace).map
        BoundaryPairingMove.slot =
      moves.map BoundaryPairingMove.slot := by
  simp [appendAll]

@[simp]
theorem prependAll_slots
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {suffixTrace : Trace params middle suffixEvents final}
    (moves : List (BoundaryPairingMove suffixTrace))
    (prefixTrace : Trace params initial prefixEvents middle) :
    (BoundaryPairingMove.prependAll moves prefixTrace).map
        BoundaryPairingMove.slot =
      moves.map BoundaryPairingMove.slot := by
  simp [prependAll]

/--
Append a suffix and immediately reindex the moves to a caller-selected proof
of the same concatenated trace.
-/
def appendAllInto
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (moves : List (BoundaryPairingMove prefixTrace))
    (suffixTrace : Trace params middle suffixEvents final)
    (targetTrace :
      Trace params initial (prefixEvents ++ suffixEvents) final) :
    List (BoundaryPairingMove targetTrace) :=
  castAll targetTrace (appendAll moves suffixTrace)

/--
Prepend a prefix and immediately reindex the moves to a caller-selected proof
of the same concatenated trace.
-/
def prependAllInto
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {suffixTrace : Trace params middle suffixEvents final}
    (moves : List (BoundaryPairingMove suffixTrace))
    (prefixTrace : Trace params initial prefixEvents middle)
    (targetTrace :
      Trace params initial (prefixEvents ++ suffixEvents) final) :
    List (BoundaryPairingMove targetTrace) :=
  castAll targetTrace (prependAll moves prefixTrace)

@[simp]
theorem appendAllInto_slots
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {prefixTrace : Trace params initial prefixEvents middle}
    (moves : List (BoundaryPairingMove prefixTrace))
    (suffixTrace : Trace params middle suffixEvents final)
    (targetTrace :
      Trace params initial (prefixEvents ++ suffixEvents) final) :
    (appendAllInto moves suffixTrace targetTrace).map
        BoundaryPairingMove.slot =
      moves.map BoundaryPairingMove.slot := by
  simp [appendAllInto]

@[simp]
theorem prependAllInto_slots
    {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {prefixEvents suffixEvents : List (Event n)}
    {suffixTrace : Trace params middle suffixEvents final}
    (moves : List (BoundaryPairingMove suffixTrace))
    (prefixTrace : Trace params initial prefixEvents middle)
    (targetTrace :
      Trace params initial (prefixEvents ++ suffixEvents) final) :
    (prependAllInto moves prefixTrace targetTrace).map
        BoundaryPairingMove.slot =
      moves.map BoundaryPairingMove.slot := by
  simp [prependAllInto]

end BoundaryPairingMove

namespace ShiftAtomicStructuralRebase

/--
A same-snapshot structural step from a shift-atomic represented state.

The exact shape change is one silent event.  Unlike the older obstruction
example, this certificate publicly retains shift atomicity of the endpoint,
so it composes with the next concrete boundary macro.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    (initial : State n) where
  transition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  finalAtomic : transition.final.ShiftAtomic
  events_eq : transition.events = [.silent]

theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {beforeTree afterTree : BST 0 n}
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        (beforeTree := beforeTree) (afterTree := afterTree) initial) := by
  let afterView := canonicalHeapView snapshot afterTree
  have rootEq : afterView.root = initial.view.root := by
    change canonicalRoot snapshot afterTree = initial.view.root
    rw [initialRepresents.view_eq]
    exact canonicalRoot_eq snapshot afterTree beforeTree
  let final := initial.rebaseShiftAtomic afterView
  have trace : Trace params initial [.silent] final :=
    initialAtomic.rebase_trace initialRepresents.valid rootEq
  have finalPrepared : final.RankPrepared params :=
    initialAtomic.rebase_rankPrepared initialRepresents.stable rootEq
  have finalStable : final.Stable params :=
    finalPrepared.stable
      (canonicalHeapView_heapOrdered snapshot afterTree)
  have finalRepresents :
      final.Represents params snapshot afterTree := by
    exact
      ⟨finalStable, State.rebaseShiftAtomic_view initial afterView⟩
  let transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial := {
    initial_represents := initialRepresents
    final := final
    events := [.silent]
    trace := trace
    final_represents := finalRepresents
  }
  exact
    ⟨{
      transition := transition
      finalAtomic := initialAtomic.rebase afterView
      events_eq := rfl
    }⟩

end ShiftAtomicStructuralRebase

namespace SplayExecutionBoundaryPairingMacro

/--
One complete splay execution realized step by step.

Every genuine zig-zig is implemented by two concrete boundary moves.  Zigs
and zig-zags use one silent structural rebase.  `firstMoves` and
`secondMoves` retain the manuscript's two chronological batches, with exact
global step indices beginning at `start`.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    {execution : SplayExecution key beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (initial : State n) (start : ℕ) where
  transition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  finalAtomic : transition.final.ShiftAtomic
  firstMoves : List (BoundaryPairingMove transition.trace)
  secondMoves : List (BoundaryPairingMove transition.trace)
  firstSlots_eq :
    firstMoves.map BoundaryPairingMove.slot =
      firstPairingsFrom start kinds
  secondSlots_eq :
    secondMoves.map BoundaryPairingMove.slot =
      secondPairingsFrom start kinds

theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {key : ℕ} {beforeTree afterTree : BST 0 n}
    {execution : SplayExecution key beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (start : ℕ) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        transcript initial start) := by
  cases transcript with
  | done root =>
      let transition := RepresentedTransition.refl initialRepresents
      exact
        ⟨{
          transition := transition
          finalAtomic := initialAtomic
          firstMoves := []
          secondMoves := []
          firstSlots_eq := by simp [firstPairingsFrom]
          secondSlots_eq := by simp [secondPairingsFrom]
        }⟩
  | zig step tail tailTranscript =>
      obtain ⟨head⟩ :=
        ShiftAtomicStructuralRebase.exists_certificate
          initialRepresents initialAtomic
      obtain ⟨rest⟩ :=
        exists_certificate tailTranscript
          head.transition.final_represents head.finalAtomic (start + 1)
      let transition := head.transition.trans rest.transition
      let firstMoves :=
        BoundaryPairingMove.prependAllInto
          rest.firstMoves head.transition.trace transition.trace
      let secondMoves :=
        BoundaryPairingMove.prependAllInto
          rest.secondMoves head.transition.trace transition.trace
      exact
        ⟨{
          transition := transition
          finalAtomic := rest.finalAtomic
          firstMoves := firstMoves
          secondMoves := secondMoves
          firstSlots_eq := by
            calc
              firstMoves.map BoundaryPairingMove.slot =
                  rest.firstMoves.map BoundaryPairingMove.slot := by
                simpa only [firstMoves] using
                  BoundaryPairingMove.prependAllInto_slots
                    rest.firstMoves head.transition.trace
                      transition.trace
              _ = firstPairingsFrom (start + 1) _ :=
                rest.firstSlots_eq
              _ = firstPairingsFrom start
                    (SplayStepKind.zig :: _) := by
                simp [firstPairingsFrom, SplayStepKind.isZigZig]
          secondSlots_eq := by
            calc
              secondMoves.map BoundaryPairingMove.slot =
                  rest.secondMoves.map BoundaryPairingMove.slot := by
                simpa only [secondMoves] using
                  BoundaryPairingMove.prependAllInto_slots
                    rest.secondMoves head.transition.trace
                      transition.trace
              _ = secondPairingsFrom (start + 1) _ :=
                rest.secondSlots_eq
              _ = secondPairingsFrom start
                    (SplayStepKind.zig :: _) := by
                simp [secondPairingsFrom, SplayStepKind.isZigZig]
        }⟩
  | zigZig step orientation tail tailTranscript =>
      obtain
          ⟨firstWinner, firstLoser, secondWinner, secondLoser,
            ⟨head⟩⟩ :=
        ZigZigBoundaryPairingMacro.exists_certificate_of_orientation
          initialRepresents initialAtomic start orientation
      obtain ⟨rest⟩ :=
        exists_certificate tailTranscript
          head.transition.final_represents head.finalAtomic (start + 1)
      let transition := head.transition.trans rest.transition
      let localFirst :
          BoundaryPairingMove head.transition.trace :=
        head.firstMove.castTrace head.transition.trace
      let localSecond :
          BoundaryPairingMove head.transition.trace :=
        head.secondMove.castTrace head.transition.trace
      let globalFirst :=
        localFirst.append rest.transition.trace
      let globalSecond :=
        localSecond.append rest.transition.trace
      let rawFirstMoves :=
        globalFirst ::
          BoundaryPairingMove.prependAll
            rest.firstMoves head.transition.trace
      let rawSecondMoves :=
        globalSecond ::
          BoundaryPairingMove.prependAll
            rest.secondMoves head.transition.trace
      let firstMoves :=
        BoundaryPairingMove.castAll transition.trace rawFirstMoves
      let secondMoves :=
        BoundaryPairingMove.castAll transition.trace rawSecondMoves
      have firstMovesSlots :
          firstMoves.map BoundaryPairingMove.slot =
            head.firstMove.slot ::
              rest.firstMoves.map BoundaryPairingMove.slot := by
        calc
          firstMoves.map BoundaryPairingMove.slot =
              rawFirstMoves.map BoundaryPairingMove.slot := by
            exact
              BoundaryPairingMove.castAll_slots
                transition.trace rawFirstMoves
          _ = head.firstMove.slot ::
                rest.firstMoves.map BoundaryPairingMove.slot := by
            simp [rawFirstMoves, globalFirst, localFirst]
      have secondMovesSlots :
          secondMoves.map BoundaryPairingMove.slot =
            head.secondMove.slot ::
              rest.secondMoves.map BoundaryPairingMove.slot := by
        calc
          secondMoves.map BoundaryPairingMove.slot =
              rawSecondMoves.map BoundaryPairingMove.slot := by
            exact
              BoundaryPairingMove.castAll_slots
                transition.trace rawSecondMoves
          _ = head.secondMove.slot ::
                rest.secondMoves.map BoundaryPairingMove.slot := by
            simp [rawSecondMoves, globalSecond, localSecond]
      exact
        ⟨{
          transition := transition
          finalAtomic := rest.finalAtomic
          firstMoves := firstMoves
          secondMoves := secondMoves
          firstSlots_eq := by
            calc
              firstMoves.map BoundaryPairingMove.slot =
                  head.firstMove.slot ::
                    rest.firstMoves.map BoundaryPairingMove.slot :=
                firstMovesSlots
              _ =
                  { zigZigStep := start, phase := .first } ::
                    firstPairingsFrom (start + 1) _ := by
                rw [head.first_slot, rest.firstSlots_eq]
              _ = firstPairingsFrom start
                    (SplayStepKind.zigZig :: _) := by
                simp [firstPairingsFrom, SplayStepKind.isZigZig]
          secondSlots_eq := by
            calc
              secondMoves.map BoundaryPairingMove.slot =
                  head.secondMove.slot ::
                    rest.secondMoves.map BoundaryPairingMove.slot :=
                secondMovesSlots
              _ =
                  { zigZigStep := start, phase := .second } ::
                    secondPairingsFrom (start + 1) _ := by
                rw [head.second_slot, rest.secondSlots_eq]
              _ = secondPairingsFrom start
                    (SplayStepKind.zigZig :: _) := by
                simp [secondPairingsFrom, SplayStepKind.isZigZig]
        }⟩
  | zigZag step orientation tail tailTranscript =>
      obtain ⟨head⟩ :=
        ShiftAtomicStructuralRebase.exists_certificate
          initialRepresents initialAtomic
      obtain ⟨rest⟩ :=
        exists_certificate tailTranscript
          head.transition.final_represents head.finalAtomic (start + 1)
      let transition := head.transition.trans rest.transition
      let firstMoves :=
        BoundaryPairingMove.prependAllInto
          rest.firstMoves head.transition.trace transition.trace
      let secondMoves :=
        BoundaryPairingMove.prependAllInto
          rest.secondMoves head.transition.trace transition.trace
      exact
        ⟨{
          transition := transition
          finalAtomic := rest.finalAtomic
          firstMoves := firstMoves
          secondMoves := secondMoves
          firstSlots_eq := by
            calc
              firstMoves.map BoundaryPairingMove.slot =
                  rest.firstMoves.map BoundaryPairingMove.slot := by
                simpa only [firstMoves] using
                  BoundaryPairingMove.prependAllInto_slots
                    rest.firstMoves head.transition.trace
                      transition.trace
              _ = firstPairingsFrom (start + 1) _ :=
                rest.firstSlots_eq
              _ = firstPairingsFrom start
                    (SplayStepKind.zigZag :: _) := by
                simp [firstPairingsFrom, SplayStepKind.isZigZig]
          secondSlots_eq := by
            calc
              secondMoves.map BoundaryPairingMove.slot =
                  rest.secondMoves.map BoundaryPairingMove.slot := by
                simpa only [secondMoves] using
                  BoundaryPairingMove.prependAllInto_slots
                    rest.secondMoves head.transition.trace
                      transition.trace
              _ = secondPairingsFrom (start + 1) _ :=
                rest.secondSlots_eq
              _ = secondPairingsFrom start
                    (SplayStepKind.zigZag :: _) := by
                simp [secondPairingsFrom, SplayStepKind.isZigZig]
        }⟩
termination_by kinds.length

end SplayExecutionBoundaryPairingMacro

namespace SplaySequenceBoundaryPairingMacro

/--
An arbitrary dependent request sequence at one fixed comparison snapshot,
with all zig-zig boundary moves composed into its single rich trace.
-/
structure Certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (initial : State n) (start : ℕ) where
  transition :
    RepresentedTransition params
      snapshot beforeTree snapshot afterTree initial
  finalAtomic : transition.final.ShiftAtomic
  firstMoves : List (BoundaryPairingMove transition.trace)
  secondMoves : List (BoundaryPairingMove transition.trace)
  firstSlots_eq :
    firstMoves.map BoundaryPairingMove.slot =
      firstPairingsFrom start kinds
  secondSlots_eq :
    secondMoves.map BoundaryPairingMove.slot =
      secondPairingsFrom start kinds

theorem exists_certificate
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    (initialRepresents :
      initial.Represents params snapshot beforeTree)
    (initialAtomic : initial.ShiftAtomic)
    (start : ℕ) :
    Nonempty
      (Certificate (params := params) (snapshot := snapshot)
        transcript initial start) := by
  cases transcript with
  | done tree =>
      let transition := RepresentedTransition.refl initialRepresents
      exact
        ⟨{
          transition := transition
          finalAtomic := initialAtomic
          firstMoves := []
          secondMoves := []
          firstSlots_eq := by simp [firstPairingsFrom]
          secondSlots_eq := by simp [secondPairingsFrom]
        }⟩
  | @next access accesses before middle after
      headKinds tailKinds headZig headZigZig headZigZag
      tailZig tailZigZig tailZigZag
      head tail headTranscript tailTranscript =>
      obtain ⟨headCertificate⟩ :=
        SplayExecutionBoundaryPairingMacro.exists_certificate
          headTranscript initialRepresents initialAtomic start
      obtain ⟨tailCertificate⟩ :=
        exists_certificate tailTranscript
          headCertificate.transition.final_represents
          headCertificate.finalAtomic (start + headKinds.length)
      let transition :=
        headCertificate.transition.trans tailCertificate.transition
      let firstMoves :=
        BoundaryPairingMove.appendAllInto
            headCertificate.firstMoves tailCertificate.transition.trace
              transition.trace ++
          BoundaryPairingMove.prependAllInto
            tailCertificate.firstMoves headCertificate.transition.trace
              transition.trace
      let secondMoves :=
        BoundaryPairingMove.appendAllInto
            headCertificate.secondMoves tailCertificate.transition.trace
              transition.trace ++
          BoundaryPairingMove.prependAllInto
            tailCertificate.secondMoves headCertificate.transition.trace
              transition.trace
      exact
        ⟨{
          transition := transition
          finalAtomic := tailCertificate.finalAtomic
          firstMoves := firstMoves
          secondMoves := secondMoves
          firstSlots_eq := by
            calc
              firstMoves.map BoundaryPairingMove.slot =
                  headCertificate.firstMoves.map
                      BoundaryPairingMove.slot ++
                    tailCertificate.firstMoves.map
                      BoundaryPairingMove.slot := by
                simp only [firstMoves, List.map_append,
                  BoundaryPairingMove.appendAllInto_slots,
                  BoundaryPairingMove.prependAllInto_slots]
              _ = firstPairingsFrom start headKinds ++
                    firstPairingsFrom
                      (start + headKinds.length) tailKinds := by
                rw [headCertificate.firstSlots_eq,
                  tailCertificate.firstSlots_eq]
              _ = firstPairingsFrom start
                    (headKinds ++ tailKinds) := by
                rw [firstPairingsFrom_append]
          secondSlots_eq := by
            calc
              secondMoves.map BoundaryPairingMove.slot =
                  headCertificate.secondMoves.map
                      BoundaryPairingMove.slot ++
                    tailCertificate.secondMoves.map
                      BoundaryPairingMove.slot := by
                simp only [secondMoves, List.map_append,
                  BoundaryPairingMove.appendAllInto_slots,
                  BoundaryPairingMove.prependAllInto_slots]
              _ = secondPairingsFrom start headKinds ++
                    secondPairingsFrom
                      (start + headKinds.length) tailKinds := by
                rw [headCertificate.secondSlots_eq,
                  tailCertificate.secondSlots_eq]
              _ = secondPairingsFrom start
                    (headKinds ++ tailKinds) := by
                rw [secondPairingsFrom_append]
        }⟩
termination_by accesses.length

/--
Atomic initialization followed by the multi-request macro gives a complete
all-important boundary/pass classification for every zig-zig slot.
-/
theorem exists_atomicInitialized_allImportant
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    let initialization :=
      Splay.Lazy.Canonical.atomicInitialization
        snapshot beforeTree params growingLimit valueBound
    ∃ certificate :
        Certificate (params := params) (snapshot := snapshot)
          transcript initialization.final 0,
      let moves := certificate.firstMoves ++ certificate.secondMoves
      Nonempty
        (BoundaryPassPairingClassification transcript params
          (Canonical.emptyCanonicalState snapshot beforeTree)
          certificate.transition.final
          (initialization.events ++ certificate.transition.events)) := by
  let initialization :=
    Splay.Lazy.Canonical.atomicInitialization
      snapshot beforeTree params growingLimit valueBound
  have initialAtomic : initialization.final.ShiftAtomic :=
    atomicInitialization_final_shiftAtomic
      snapshot beforeTree params growingLimit valueBound
  obtain ⟨certificate⟩ :=
    exists_certificate transcript initialization.final_represents
      initialAtomic 0
  let moves := certificate.firstMoves ++ certificate.secondMoves
  have movesSlots :
      moves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds := by
    simp only [moves, List.map_append]
    rw [certificate.firstSlots_eq, certificate.secondSlots_eq]
    simp
  let classification :=
    BoundaryPassPairingClassification.ofInitializedAllImportantSuffix
      (params := params) (snapshot := snapshot)
      (initializedTree := beforeTree)
      transcript initialization certificate.transition.trace
      moves movesSlots
  exact ⟨certificate, ⟨classification⟩⟩

end SplaySequenceBoundaryPairingMacro

end Splay.Accounting
