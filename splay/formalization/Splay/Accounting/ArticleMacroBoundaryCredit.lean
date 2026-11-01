import Splay.Accounting.ArticlePairingBoundaryEstimate
import Splay.Accounting.ArticleGlobalUnbroken

namespace Splay.Lazy

theorem Trace.boundaryCredit_of_births {n cutoff budget : ℕ} {params : Interface.Parameters}
    {before after : State n} {events : List (Event n)} (trace : Trace params before events after)
    (births : after.blocks.length ≤ before.blocks.length + budget) :
    Interface.boundaryCredit cutoff after.toInterface ≤ Interface.boundaryCredit cutoff before.toInterface +
      Interface.boundaryCreditCapacity cutoff * budget := by
  have count := trace.blocks_length_eq
  have growth : Interface.totalBlockGrowth (eraseOperations events) ≤ budget := by omega
  exact trace.toInterface.boundaryCredit_bound.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ growth) _)

end Splay.Lazy

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

variable {n cutoff : ℕ} {params : Interface.Parameters}
  (exempt : params.exemptPasses = 2) (numerator : params.matchingNumerator = 1)
  (denominator : params.matchingDenominator = 8)

include exempt numerator denominator

theorem ArticleCompleteRequest.boundary_credit_estimate
    {comparison before after : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (request : ArticleCompleteRequest params comparison before after key kinds initial)
    (root : comparison.HasRoot key.val) {execution : SplayExecution key.val before after}
    {zig zigZig zigZag : ℕ} (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree comparison).withTruePriority before initial) :
    cutoff * (2 * request.stage.pairing.boundaryCount) +
      4 * cutoff * Interface.boundaryCredit cutoff request.final.toInterface ≤
        4 * cutoff * Interface.boundaryCredit cutoff initial.toInterface +
          4 * cutoff * Interface.boundaryCreditCapacity cutoff *
            (32 + articleRestorationBirthBudget request.stage.restorationJunctionBound) +
          16 * Interface.totalActivity (eraseOperations request.events) := by
  have prepared := request.stage.pairing.preparation.preservesUnbroken
    (request.stage.setup.preservesUnbroken unbroken)
  have pairing := request.stage.pairing.boundary_credit_estimate (cutoff := cutoff)
    transcript exempt numerator denominator prepared
  have setup := request.stage.setup.trace.boundaryCredit_of_births (cutoff := cutoff) request.stage.setup.births
  have transfers := request.stage.transferTrace_stable.1.toInterface.boundaryCredit_bound (cutoff := cutoff)
  have transferPaid : Interface.boundaryCredit cutoff request.stage.final.toInterface ≤
      Interface.boundaryCredit cutoff request.stage.pairing.final.toInterface := by
    simpa only [eraseOperations, Event.operations, List.flatMap_cons, List.flatMap_nil,
      List.nil_append, Interface.totalBlockGrowth, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] using transfers
  have restoration := request.restoration.trace.boundaryCredit_of_births (cutoff := cutoff) request.restoration.births
  have canonicalCredit : Interface.boundaryCredit cutoff (request.stage.canonicalFinal after).toInterface =
      Interface.boundaryCredit cutoff request.stage.final.toInterface := rfl
  rw [canonicalCredit] at restoration
  change Interface.boundaryCredit cutoff request.final.toInterface ≤ _ at restoration
  have activityLe : Interface.totalActivity (eraseOperations request.stage.pairing.events) ≤
      Interface.totalActivity (eraseOperations request.events) := by
    rw [request.erased_events, request.stage.erased_events, Interface.totalActivity_append,
      Interface.totalActivity_append]
    omega
  have setupWeighted := Nat.mul_le_mul_left (4 * cutoff) setup
  have transferWeighted := Nat.mul_le_mul_left (4 * cutoff) transferPaid
  have restorationWeighted := Nat.mul_le_mul_left (4 * cutoff) restoration
  nlinarith

theorem ArticleMacro.boundary_credit_estimate {before after : ArticleCheckpoint n}
    (step : ArticleMacro params before after)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree before.comparison).withTruePriority before.splay before.state) :
    cutoff * (2 * step.boundaryCount) +
      4 * cutoff * Interface.boundaryCredit cutoff after.state.toInterface ≤
        4 * cutoff * Interface.boundaryCredit cutoff before.state.toInterface +
          4 * cutoff * Interface.boundaryCreditCapacity cutoff * step.birthBudget +
          16 * Interface.totalActivity (eraseOperations step.events) := by
  cases step with
  | rotation represented rotation execution =>
    have paid := execution.trace.boundaryCredit_of_births (cutoff := cutoff) execution.births
    have weighted := Nat.mul_le_mul_left (4 * cutoff) paid
    simp only [boundaryCount, birthBudget, events, Nat.mul_zero, Nat.zero_add]
    nlinarith
  | request represented root execution transcript request =>
    exact request.boundary_credit_estimate exempt numerator denominator root transcript.transcript unbroken

theorem ArticleMacroHistory.boundary_credit_estimate {first last : ArticleCheckpoint n}
    (history : ArticleMacroHistory params first last)
    (zero : Interface.GrowingPassCountZero first.state.toInterface)
    (unbroken : PassedBlocksUnbroken (Snapshot.ofTree first.comparison).withTruePriority first.splay first.state) :
    cutoff * (2 * history.boundaryCount) +
      4 * cutoff * Interface.boundaryCredit cutoff last.state.toInterface ≤
        4 * cutoff * Interface.boundaryCredit cutoff first.state.toInterface +
          4 * cutoff * Interface.boundaryCreditCapacity cutoff * history.birthBudget +
          16 * Interface.totalActivity (eraseOperations history.events) := by
  induction history with
  | done => simp [boundaryCount, birthBudget, events, eraseOperations, Interface.totalActivity]
  | next head tail ih =>
    have firstPaid := head.boundary_credit_estimate exempt numerator denominator (cutoff := cutoff) unbroken
    have restPaid := ih (head.trace.growingPassCountZero zero) (head.preservesUnbroken zero unbroken)
    simp only [boundaryCount, birthBudget, events, eraseOperations_append, Interface.totalActivity_append]
    nlinarith

end Splay.Accounting
