import Splay.Accounting.ZigZigBoundaryPairingMacro
import Splay.Lazy.AtomicInitialization

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

namespace BoundaryPassPairingClassification

/--
Build the global pass/boundary classification when every zig-zig pairing slot
is implemented by a supplied chronological boundary move.

The activity history is generated automatically from the initialized trace.
There are no internal pass charges and no unimportant boundary slots, so the
only substantive premise is the exact slot list carried by `moves`.
-/
noncomputable def ofAllImportant
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (initialState : initial.toInterface.Initial params)
    (trace : Trace params initial events final)
    (moves : List (BoundaryPairingMove trace))
    (movesSlots :
      moves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds) :
    BoundaryPassPairingClassification transcript params
      initial final events := by
  let grouping :=
    exists_activityGrouping_for_pairingClassification
      initialState trace.toInterface
  let finalLabels := Classical.choose grouping
  let activityOccurrences :=
    Classical.choose (Classical.choose_spec grouping)
  have activityHistory :
      Interface.ActivityHistory params initial.toInterface []
        (eraseOperations events) activityOccurrences
        final.toInterface finalLabels :=
    (Classical.choose_spec (Classical.choose_spec grouping)).1
  let passClassification :
      PassPairingClassification transcript params
        initial.toInterface final.toInterface
        (eraseOperations events) := {
    initialState := initialState
    trace := trace.toInterface
    finalLabels := finalLabels
    activityOccurrences := activityOccurrences
    activityHistory := activityHistory
    importantSlots := firstPairings kinds ++ secondPairings kinds
    unimportantSlots := []
    internalCharges := []
    slots_partition := by simp
    internalActivityOrdinals_nodup := by simp
  }
  exact
    { trace := trace
      passClassification := passClassification
      importantMoves := moves
      unimportantMoves := []
      importantSlots_eq := movesSlots
      unimportantSlots_eq := by simp [passClassification] }

/--
Prepend a checked empty-block initialization to an all-boundary suffix.

Every supplied move is transported through the initialization prefix; its
slot and endpoints are unchanged and its two event indices are shifted by
the exact prefix length.
-/
noncomputable def ofInitializedAllImportantSuffix
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {params : Interface.Parameters}
    {snapshot : Snapshot n} {initializedTree : BST 0 n}
    (initialization : Initialization params snapshot initializedTree)
    {final : State n} {suffixEvents : List (Event n)}
    (suffixTrace :
      Trace params initialization.final suffixEvents final)
    (moves : List (BoundaryPairingMove suffixTrace))
    (movesSlots :
      moves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds) :
    BoundaryPassPairingClassification transcript params
      (Canonical.emptyCanonicalState snapshot initializedTree)
      final (initialization.events ++ suffixEvents) := by
  let fullTrace := initialization.trace.append suffixTrace
  let prefixedMoves :=
    moves.map fun move =>
      move.prepend initialization.trace
  have prefixedSlots :
      prefixedMoves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds := by
    have slotFunction :
        (fun move : BoundaryPairingMove suffixTrace =>
          (move.prepend initialization.trace).slot) =
        (fun move : BoundaryPairingMove suffixTrace =>
          move.slot) := by
      funext move
      exact move.prepend_slot initialization.trace
    dsimp only [prefixedMoves]
    rw [List.map_map]
    change
      moves.map
          (fun move : BoundaryPairingMove suffixTrace =>
            (move.prepend initialization.trace).slot) =
        firstPairings kinds ++ secondPairings kinds
    rw [slotFunction]
    exact movesSlots
  exact
    ofAllImportant transcript
      initialization.initial_toInterface_initial
      fullTrace prefixedMoves prefixedSlots

end BoundaryPassPairingClassification

/-- The productive atomic initialization ends in shift-atomic normal form. -/
theorem atomicInitialization_final_shiftAtomic
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (Splay.Lazy.Canonical.atomicInitialization snapshot tree params
      growingLimit valueBound).final.ShiftAtomic := by
  change
    (Splay.Lazy.Canonical.atomicPopulation snapshot tree params
      growingLimit valueBound).final.ShiftAtomic
  exact
    (Splay.Lazy.Canonical.atomicPopulation snapshot tree params
      growingLimit valueBound).shiftAtomic

/--
A single genuine zig-zig whose transcript has exactly its two pairing slots
admits a fully initialized `BoundaryPassPairingClassification`.

This is the end-to-end all-boundary specialization: atomic initialization is
chosen automatically, both canonical endpoint pairs are extracted from the
orientation, both delete/insert macros are executed, and the initialized
activity history is generated from the resulting trace.
-/
theorem exists_atomicInitialized_singleZigZig_allImportant
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {params : Interface.Parameters} {snapshot : Snapshot n}
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound)
    {depth key : ℕ}
    (zigZigStep : ℕ)
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key)
        beforeTree afterTree)
    (allSlots_eq :
      firstPairings kinds ++ secondPairings kinds =
        [{ zigZigStep := zigZigStep, phase := .first },
          { zigZigStep := zigZigStep, phase := .second }]) :
    let initialization :=
      Splay.Lazy.Canonical.atomicInitialization
        snapshot beforeTree params growingLimit valueBound
    ∃ firstWinner firstLoser secondWinner secondLoser,
      ∃ certificate :
          ZigZigBoundaryPairingMacro.Certificate
            (params := params) (snapshot := snapshot)
            (beforeTree := beforeTree) (afterTree := afterTree)
            (depth := depth) (key := key)
            initialization.final zigZigStep
            firstWinner firstLoser secondWinner secondLoser,
        Nonempty
          (BoundaryPassPairingClassification transcript params
            (Canonical.emptyCanonicalState snapshot beforeTree)
            certificate.transition.final
            (initialization.events ++ certificate.transition.events)) := by
  let initialization :=
    Splay.Lazy.Canonical.atomicInitialization
      snapshot beforeTree params growingLimit valueBound
  have initializationAtomic : initialization.final.ShiftAtomic := by
    exact
      atomicInitialization_final_shiftAtomic
        snapshot beforeTree params growingLimit valueBound
  obtain
      ⟨firstWinner, firstLoser, secondWinner, secondLoser,
        ⟨certificate⟩⟩ :=
    ZigZigBoundaryPairingMacro.exists_certificate_of_orientation
      initialization.final_represents initializationAtomic
      zigZigStep orientation
  let moves := [certificate.firstMove, certificate.secondMove]
  have movesSlots :
      moves.map BoundaryPairingMove.slot =
        firstPairings kinds ++ secondPairings kinds := by
    change
      [certificate.firstMove.slot, certificate.secondMove.slot] =
        firstPairings kinds ++ secondPairings kinds
    rw [certificate.first_slot, certificate.second_slot]
    exact allSlots_eq.symm
  let classification :=
    BoundaryPassPairingClassification.ofInitializedAllImportantSuffix
      transcript initialization certificate.transition.trace
      moves movesSlots
  exact
    ⟨firstWinner, firstLoser, secondWinner, secondLoser,
      certificate, ⟨classification⟩⟩

end Splay.Accounting
