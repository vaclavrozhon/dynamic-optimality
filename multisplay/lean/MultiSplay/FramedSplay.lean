import MultiSplay.InterfaceFramedTrace
import Splay.Accounting.ArticleMacroHistory

/-!
# Actual splay and comparison realizations inside the shared forest history

Every macro comes from the existing constructive article realization. Its
strict operations are replayed in the current global state with identical
charges. Local geometric-potential inequalities therefore transfer to one
global excess potential, independent of the sizes of the active components.
-/

namespace MultiSplay.FramedSplay

open Splay.Accounting Splay.Lazy Splay.Rank Splay.Tree.BST

variable {n m : Nat} {params : Splay.Interface.Parameters}

theorem excess_charge_transfer
    {a a' : Splay.Interface.State n} {b b' : Splay.Interface.State m}
    {localWord : List (Splay.Interface.Operation n)} {globalWord : List (Splay.Interface.Operation m)}
    (localRun : Splay.Interface.Trace params a localWord a')
    (globalRun : Splay.Interface.Trace params b globalWord b') (valid : b.Valid params)
    (increases : Splay.Interface.totalIncreases globalWord = Splay.Interface.totalIncreases localWord)
    (decreases : Splay.Interface.totalDecreases globalWord = Splay.Interface.totalDecreases localWord)
    {charge budget : Nat} (paid : a'.totalValue + charge ≤ a.totalValue + budget) :
    InterfaceForest.excess b' + charge ≤ InterfaceForest.excess b + budget := by
  have localBalance := localRun.totalValue_balance
  have globalBalance := InterfaceForest.excess_balance valid globalRun
  rw [increases, decreases] at globalBalance
  omega

structure Realization {before after : ArticleCheckpoint n} (step : ArticleMacro params before after)
    (whole : Splay.Interface.State m)
    (initial : InterfaceFramedTrace.Framed params before.state.toInterface whole) where
  final : Splay.Interface.State m
  operations : List (Splay.Interface.Operation m)
  trace : Splay.Interface.Trace params whole operations final
  framed : InterfaceFramedTrace.Framed params after.state.toInterface final
  element_eq : framed.element = initial.element
  frame_eq : framed.frame = initial.frame
  activity_eq : Splay.Interface.totalActivity operations = Splay.Interface.totalActivity (eraseOperations step.events)
  inserts_eq : Splay.Interface.totalInserts operations = Splay.Interface.totalInserts (eraseOperations step.events)
  increases_eq : Splay.Interface.totalIncreases operations = Splay.Interface.totalIncreases (eraseOperations step.events)
  decreases_eq : Splay.Interface.totalDecreases operations = Splay.Interface.totalDecreases (eraseOperations step.events)

theorem exists_macro {before after : ArticleCheckpoint n} (step : ArticleMacro params before after)
    (whole : Splay.Interface.State m)
    (initial : InterfaceFramedTrace.Framed params before.state.toInterface whole) :
    Nonempty (Realization step whole initial) := by
  obtain ⟨word, final, execution, ⟨next, elementEq, frameEq⟩, _, activity, inserts, increases, decreases⟩ :=
    initial.trace step.trace.toInterface
  exact ⟨⟨final, word, execution, next, elementEq, frameEq, activity, inserts, increases, decreases⟩⟩

theorem Realization.inserts {before after : ArticleCheckpoint n} {step : ArticleMacro params before after}
    {whole : Splay.Interface.State m} {initial : InterfaceFramedTrace.Framed params before.state.toInterface whole}
    (run : Realization step whole initial) :
    Splay.Interface.totalInserts run.operations ≤ step.rotationCount + 2 * step.boundaryCount := by
  rw [run.inserts_eq]
  exact step.inserts

theorem Realization.increases {before after : ArticleCheckpoint n} {step : ArticleMacro params before after}
    {whole : Splay.Interface.State m} {initial : InterfaceFramedTrace.Framed params before.state.toInterface whole}
    (run : Realization step whole initial) :
    Splay.Interface.totalIncreases run.operations ≤ step.goodCount +
      8 * params.valueBound * step.boundaryCount + 3 * params.valueBound * step.rotationCount := by
  rw [run.increases_eq]
  exact step.increases

/-- The good-pair charge is paid by the same global potential before and after
all component operations, including operations performed after common splits. -/
theorem Realization.good_charge {before after : ArticleCheckpoint n} {step : ArticleMacro params before after}
    {whole : Splay.Interface.State m} {initial : InterfaceFramedTrace.Framed params before.state.toInterface whole}
    (run : Realization step whole initial) :
    InterfaceForest.excess run.final + step.goodCount ≤ InterfaceForest.excess whole +
      8 * params.valueBound * step.boundaryCount + 3 * params.valueBound * step.rotationCount := by
  rw [Nat.add_assoc]
  apply excess_charge_transfer step.trace.toInterface run.trace
    (initial.valid step.initial_represents.valid.1) run.increases_eq run.decreases_eq
  have paid := step.gap_pays_good
  rw [geometricGapPotential_eq step.initial_represents.complete step.initial_represents.valuesRealizeGaps,
    geometricGapPotential_eq step.final_represents.complete step.final_represents.valuesRealizeGaps] at paid
  simpa only [Nat.add_assoc] using paid

theorem Realization.zigZigs {before after : ArticleCheckpoint n} {step : ArticleMacro params before after}
    {whole : Splay.Interface.State m} {initial : InterfaceFramedTrace.Framed params before.state.toInterface whole}
    (run : Realization step whole initial) :
    2 * step.kinds.count .zigZig ≤ Splay.Interface.totalActivity run.operations + Splay.Interface.totalInserts run.operations := by
  rw [run.activity_eq, run.inserts_eq]
  exact step.zigZigs_le_activity_add_inserts

/-- Construct the request witness from the actual splay execution, then replay
it globally. No pairing, local-cost, or execution-existence certificate is an input. -/
theorem exists_request {comparison before after : BST 0 n} {key : Fin n} {state : Splay.Lazy.State n}
    (represented : state.Represents params (Snapshot.ofTree comparison).withTruePriority before)
    (root : comparison.HasRoot key.val) (execution : SplayExecution key.val before after)
    (valueBound : Splay.Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound)
    (whole : Splay.Interface.State m) (framed : InterfaceFramedTrace.Framed params state.toInterface whole) :
    ∃ final : Splay.Lazy.State n, ∃ step : ArticleMacro params ⟨comparison, before, state⟩ ⟨comparison, after, final⟩,
      step.requests = [key] ∧ Nonempty (Realization step whole framed) := by
  let transcript := splayExecutionTranscriptWitness execution
  obtain ⟨request⟩ := ArticleCompleteRequest.exists_of_transcript root transcript.transcript represented valueBound
  let step : ArticleMacro params ⟨comparison, before, state⟩ ⟨comparison, after, request.final⟩ :=
    .request (before := ⟨comparison, before, state⟩) represented root execution transcript request
  exact ⟨request.final, step, rfl, exists_macro step whole framed⟩

theorem exists_rotation {before after splay : BST 0 n} {depth : Nat} {state : Splay.Lazy.State n}
    (represented : state.Represents params (Snapshot.ofTree before).withTruePriority splay)
    (rotation : RotationAt depth before after)
    (whole : Splay.Interface.State m) (framed : InterfaceFramedTrace.Framed params state.toInterface whole) :
    ∃ final : Splay.Lazy.State n, ∃ step : ArticleMacro params ⟨before, splay, state⟩ ⟨after, splay, final⟩,
      step.rotationCount = 1 ∧ Nonempty (Realization step whole framed) := by
  obtain ⟨execution⟩ := ArticleComparisonExecution.exists_of_rotation rotation represented
  let step : ArticleMacro params ⟨before, splay, state⟩ ⟨after, splay, execution.final⟩ := .rotation (before := ⟨before, splay, state⟩) represented rotation execution
  exact ⟨execution.final, step, rfl, exists_macro step whole framed⟩

end MultiSplay.FramedSplay
