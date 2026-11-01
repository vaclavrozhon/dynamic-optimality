import Splay.Accounting.ArticleCompleteRequest
import Splay.Accounting.ArticleComparisonExecution

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy

/-- A stable checkpoint records both actual trees and their lazy representation. -/
structure ArticleCheckpoint (n : ℕ) where
  comparison : BST 0 n
  splay : BST 0 n
  state : Lazy.State n

def ArticleCheckpoint.Represents {n : ℕ} (checkpoint : ArticleCheckpoint n)
    (params : Interface.Parameters) : Prop :=
  checkpoint.state.Represents params (Snapshot.ofTree checkpoint.comparison).withTruePriority checkpoint.splay

/-- Actual local executions, retaining their pairing and transcript witnesses. -/
inductive ArticleMacro {n : ℕ} (params : Interface.Parameters) :
    ArticleCheckpoint n → ArticleCheckpoint n → Type
  | rotation {before : ArticleCheckpoint n} {after : BST 0 n} {depth : ℕ}
      (represented : before.Represents params)
      (rotation : RotationAt depth before.comparison after)
      (execution : ArticleComparisonExecution params before.state after before.splay depth) :
      ArticleMacro params before ⟨after, before.splay, execution.final⟩
  | request {before : ArticleCheckpoint n} {after : BST 0 n} {key : Fin n}
      (represented : before.Represents params)
      (root : before.comparison.HasRoot key.val)
      (execution : SplayExecution key.val before.splay after)
      (transcript : SplayExecutionTranscriptWitness execution)
      (request : ArticleCompleteRequest params before.comparison before.splay after key transcript.kinds before.state) :
      ArticleMacro params before ⟨before.comparison, after, request.final⟩

namespace ArticleMacro

variable {n : ℕ} {params : Interface.Parameters} {before after : ArticleCheckpoint n}

noncomputable def events : ArticleMacro params before after → List (Event n)
  | .rotation _ _ execution => execution.events
  | .request _ _ _ _ realization => realization.events

def requests : ArticleMacro params before after → List (Fin n)
  | .rotation _ _ _ => []
  | .request (key := key) _ _ _ _ _ => [key]

def kinds : ArticleMacro params before after → List SplayStepKind
  | .rotation _ _ _ => []
  | .request _ _ _ transcript _ => transcript.kinds

def rotationCount : ArticleMacro params before after → ℕ
  | .rotation _ _ _ => 1
  | .request _ _ _ _ _ => 0

noncomputable def birthBudget : ArticleMacro params before after → ℕ
  | .rotation (depth := depth) _ _ _ => articleFullComparisonBirthBudget depth
  | .request _ _ _ _ realization => 32 + articleRestorationBirthBudget realization.stage.restorationJunctionBound

noncomputable def goodCount : ArticleMacro params before after → ℕ
  | .rotation _ _ _ => 0
  | .request _ _ _ _ realization => realization.stage.pairing.internal.chain.goodCount

noncomputable def boundaryCount : ArticleMacro params before after → ℕ
  | .rotation _ _ _ => 0
  | .request _ _ _ _ realization => realization.stage.pairing.boundaryCount

theorem initial_represents (step : ArticleMacro params before after) : before.Represents params := by
  cases step <;> assumption

theorem final_represents (step : ArticleMacro params before after) : after.Represents params := by
  cases step with
  | rotation represented rotation execution => exact execution.represents
  | request represented root execution transcript request => exact request.represents

theorem trace (step : ArticleMacro params before after) : Trace params before.state step.events after.state := by
  cases step with
  | rotation represented rotation execution => exact execution.trace
  | request represented root execution transcript request => exact request.trace root transcript.transcript

theorem births (step : ArticleMacro params before after) :
    after.state.blocks.length ≤ before.state.blocks.length + step.birthBudget := by
  cases step with
  | rotation represented rotation execution => exact execution.births
  | request represented root execution transcript request => simpa only [birthBudget, Nat.add_assoc] using request.births

theorem inserts (step : ArticleMacro params before after) :
    Interface.totalInserts (eraseOperations step.events) ≤ step.rotationCount + 2 * step.boundaryCount := by
  cases step with
  | rotation represented rotation execution => simpa only [events, rotationCount, boundaryCount, Nat.mul_zero, Nat.add_zero] using execution.inserts
  | request represented root execution transcript request => simp only [events, rotationCount, boundaryCount, Nat.zero_add, request.inserts, le_refl]

theorem increases (step : ArticleMacro params before after) :
    Interface.totalIncreases (eraseOperations step.events) ≤ step.goodCount +
      8 * params.valueBound * step.boundaryCount + 3 * params.valueBound * step.rotationCount := by
  cases step with
  | rotation represented rotation execution => simpa only [events, goodCount, boundaryCount, rotationCount, Nat.mul_zero, Nat.mul_one, Nat.zero_add] using execution.increases
  | request represented root execution transcript request => simpa only [events, goodCount, boundaryCount, rotationCount, Nat.mul_zero, Nat.add_zero] using request.increases

theorem gap_pays_good (step : ArticleMacro params before after) :
    geometricGapPotential after.state + step.goodCount ≤ geometricGapPotential before.state +
      8 * params.valueBound * step.boundaryCount + 3 * params.valueBound * step.rotationCount := by
  cases step with
  | rotation represented rotation execution =>
      have balance := execution.trace.toInterface.totalValue_balance
      rw [← geometricGapPotential_eq represented.stable.2.1 represented.stable.2.2.2.2.2,
        ← geometricGapPotential_eq execution.represents.stable.2.1 execution.represents.stable.2.2.2.2.2] at balance
      have bound := execution.increases
      simp only [goodCount, boundaryCount, rotationCount, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      omega
  | request represented root execution transcript request =>
      simpa only [goodCount, boundaryCount, rotationCount, Nat.mul_zero, Nat.add_zero] using request.gap_pays_good root transcript.transcript

theorem zigZigs_le_activity_add_inserts (step : ArticleMacro params before after) :
    2 * step.kinds.count .zigZig ≤ Interface.totalActivity (eraseOperations step.events) +
      Interface.totalInserts (eraseOperations step.events) := by
  cases step with
  | rotation represented rotation execution => simp [kinds]
  | request represented root execution transcript request => exact request.zigZigs_le_activity_add_inserts

end ArticleMacro

/-- The chronological trace keeps all intermediate represented states and all
local witnesses; neither empty requests nor root-changing rotations are dropped. -/
inductive ArticleMacroHistory {n : ℕ} (params : Interface.Parameters) :
    ArticleCheckpoint n → ArticleCheckpoint n → Type
  | done (checkpoint : ArticleCheckpoint n) (represented : checkpoint.Represents params) :
      ArticleMacroHistory params checkpoint checkpoint
  | next {first middle last : ArticleCheckpoint n}
      (head : ArticleMacro params first middle) (tail : ArticleMacroHistory params middle last) :
      ArticleMacroHistory params first last

namespace ArticleMacroHistory

variable {n : ℕ} {params : Interface.Parameters} {first middle last : ArticleCheckpoint n}

noncomputable def events {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → List (Event n)
  | .done _ _ => []
  | .next head tail => head.events ++ tail.events

def requests {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → List (Fin n)
  | .done _ _ => []
  | .next head tail => head.requests ++ tail.requests

def kinds {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → List SplayStepKind
  | .done _ _ => []
  | .next head tail => head.kinds ++ tail.kinds

def rotationCount {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → ℕ
  | .done _ _ => 0
  | .next head tail => head.rotationCount + tail.rotationCount

noncomputable def birthBudget {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → ℕ
  | .done _ _ => 0
  | .next head tail => head.birthBudget + tail.birthBudget

noncomputable def goodCount {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → ℕ
  | .done _ _ => 0
  | .next head tail => head.goodCount + tail.goodCount

noncomputable def boundaryCount {first last : ArticleCheckpoint n} : ArticleMacroHistory params first last → ℕ
  | .done _ _ => 0
  | .next head tail => head.boundaryCount + tail.boundaryCount

def append {first middle : ArticleCheckpoint n} (left : ArticleMacroHistory params first middle)
    (right : ArticleMacroHistory params middle last) : ArticleMacroHistory params first last :=
  match left with
  | .done _ _ => right
  | .next head tail => .next head (tail.append right)

@[simp] theorem events_append (left : ArticleMacroHistory params first middle) (right : ArticleMacroHistory params middle last) :
    (left.append right).events = left.events ++ right.events := by
  induction left with
  | done => rfl
  | next head tail ih => simp [append, events, ih, List.append_assoc]

@[simp] theorem requests_append (left : ArticleMacroHistory params first middle) (right : ArticleMacroHistory params middle last) :
    (left.append right).requests = left.requests ++ right.requests := by
  induction left with
  | done => rfl
  | next head tail ih => simp [append, requests, ih, List.append_assoc]

@[simp] theorem kinds_append (left : ArticleMacroHistory params first middle) (right : ArticleMacroHistory params middle last) :
    (left.append right).kinds = left.kinds ++ right.kinds := by
  induction left with
  | done => rfl
  | next head tail ih => simp [append, kinds, ih, List.append_assoc]

@[simp] theorem rotationCount_append (left : ArticleMacroHistory params first middle) (right : ArticleMacroHistory params middle last) :
    (left.append right).rotationCount = left.rotationCount + right.rotationCount := by
  induction left with
  | done => simp [append, rotationCount]
  | next head tail ih => simp [append, rotationCount, ih, Nat.add_assoc]

theorem final_represents (history : ArticleMacroHistory params first last) : last.Represents params := by
  induction history with
  | done _ represented => exact represented
  | next _ _ ih => exact ih

theorem trace (history : ArticleMacroHistory params first last) : Trace params first.state history.events last.state := by
  induction history with
  | done _ represented => exact .nil represented.valid
  | next head tail ih => exact head.trace.append ih

theorem births (history : ArticleMacroHistory params first last) :
    last.state.blocks.length ≤ first.state.blocks.length + history.birthBudget := by
  induction history with
  | done => simp [birthBudget]
  | next head tail ih => have := head.births; simp only [birthBudget]; omega

theorem inserts (history : ArticleMacroHistory params first last) :
    Interface.totalInserts (eraseOperations history.events) ≤ history.rotationCount + 2 * history.boundaryCount := by
  induction history with
  | done => simp [events, rotationCount, boundaryCount, eraseOperations, Interface.totalInserts]
  | next head tail ih =>
      have := head.inserts
      simp only [events, eraseOperations_append, Interface.totalInserts_append, rotationCount, boundaryCount]
      omega

theorem increases (history : ArticleMacroHistory params first last) :
    Interface.totalIncreases (eraseOperations history.events) ≤ history.goodCount +
      8 * params.valueBound * history.boundaryCount + 3 * params.valueBound * history.rotationCount := by
  induction history with
  | done => simp [events, goodCount, boundaryCount, rotationCount, eraseOperations, Interface.totalIncreases]
  | next head tail ih =>
      have := head.increases
      simp only [events, eraseOperations_append, Interface.totalIncreases_append, rotationCount, goodCount, boundaryCount, Nat.mul_add]
      omega

theorem gap_pays_good (history : ArticleMacroHistory params first last) :
    geometricGapPotential last.state + history.goodCount ≤ geometricGapPotential first.state +
      8 * params.valueBound * history.boundaryCount + 3 * params.valueBound * history.rotationCount := by
  induction history with
  | done => simp [goodCount, boundaryCount, rotationCount]
  | next head tail ih =>
      have := head.gap_pays_good
      simp only [goodCount, boundaryCount, rotationCount, Nat.mul_add]
      omega

theorem zigZigs_le_activity_add_inserts (history : ArticleMacroHistory params first last) :
    2 * history.kinds.count .zigZig ≤ Interface.totalActivity (eraseOperations history.events) +
      Interface.totalInserts (eraseOperations history.events) := by
  induction history with
  | done => simp [kinds]
  | next head tail ih =>
      have := head.zigZigs_le_activity_add_inserts
      simp only [kinds, List.count_append, events, eraseOperations_append, Interface.totalActivity_append, Interface.totalInserts_append]
      omega

end ArticleMacroHistory
end Splay.Accounting
