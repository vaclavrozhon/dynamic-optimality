import Splay.Accounting.ArticleMacroBirthBounds
import Splay.Lazy.NormalFormSchedule

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy Splay.Assumptions.NormalForm

/-- A finite chronological realization with exact requests and rotation count,
and a creation budget depending only on the two uniform local constants. -/
structure ArticleChronologicalExecution {n : ℕ} (params : Interface.Parameters)
    (initial : ArticleCheckpoint n) (comparison splay : BST 0 n)
    (accesses : List (Fin n)) (rotations requestBudget rotationBudget : ℕ) where
  final : Lazy.State n
  history : ArticleMacroHistory params initial ⟨comparison, splay, final⟩
  requests_eq : history.requests = accesses
  rotations_eq : history.rotationCount = rotations
  budget : history.birthBudget ≤ requestBudget * accesses.length + rotationBudget * rotations

namespace ArticleChronologicalExecution

variable {n : ℕ} {params : Interface.Parameters} {initial : ArticleCheckpoint n}
  {comparison splay : BST 0 n} {accesses : List (Fin n)} {rotations requestBudget rotationBudget : ℕ}

def done (represented : initial.Represents params) :
    ArticleChronologicalExecution params initial initial.comparison initial.splay [] 0 requestBudget rotationBudget where
  final := initial.state
  history := .done initial represented
  requests_eq := rfl
  rotations_eq := rfl
  budget := Nat.zero_le _

def append (left : ArticleChronologicalExecution params initial comparison splay accesses rotations requestBudget rotationBudget)
    {comparisonAfter splayAfter : BST 0 n} {later : List (Fin n)} {laterRotations : ℕ}
    (right : ArticleChronologicalExecution params ⟨comparison, splay, left.final⟩ comparisonAfter splayAfter
      later laterRotations requestBudget rotationBudget) :
    ArticleChronologicalExecution params initial comparisonAfter splayAfter (accesses ++ later)
      (rotations + laterRotations) requestBudget rotationBudget where
  final := right.final
  history := left.history.append right.history
  requests_eq := by rw [ArticleMacroHistory.requests_append, left.requests_eq, right.requests_eq]
  rotations_eq := by rw [ArticleMacroHistory.rotationCount_append, left.rotations_eq, right.rotations_eq]
  budget := by
    rw [ArticleMacroHistory.birthBudget_append, List.length_append, Nat.mul_add, Nat.mul_add]
    have first := left.budget
    have second := right.budget
    omega

theorem represents (execution : ArticleChronologicalExecution params initial comparison splay accesses rotations requestBudget rotationBudget) :
    execution.final.Represents params (Snapshot.ofTree comparison).withTruePriority splay :=
  execution.history.final_represents

theorem births (execution : ArticleChronologicalExecution params initial comparison splay accesses rotations requestBudget rotationBudget) :
    execution.final.blocks.length ≤ initial.state.blocks.length + requestBudget * accesses.length + rotationBudget * rotations := by
  have actual := execution.history.births
  change execution.final.blocks.length ≤ initial.state.blocks.length + execution.history.birthBudget at actual
  have budget := execution.budget
  omega

theorem exists_rotation {after : BST 0 n} {depth depthBound slack : ℕ}
    (represented : initial.Represents params)
    (rotation : RotationAt depth initial.comparison after) (depth_le : depth ≤ depthBound) :
    Nonempty (ArticleChronologicalExecution params initial after initial.splay [] 1
      (articleRequestBirthBudget slack) (articleFullComparisonBirthBudget depthBound)) := by
  obtain ⟨execution⟩ := ArticleComparisonExecution.exists_of_rotation rotation represented
  let step : ArticleMacro params initial ⟨after, initial.splay, execution.final⟩ := .rotation represented rotation execution
  refine ⟨{
    final := execution.final
    history := .next step (.done _ execution.represents)
    requests_eq := rfl
    rotations_eq := rfl
    budget := ?_
  }⟩
  simpa only [ArticleMacroHistory.birthBudget, step, ArticleMacro.birthBudget,
    Nat.add_zero, List.length_nil, Nat.mul_zero, Nat.mul_one, Nat.zero_add] using
    articleFullComparisonBirthBudget_mono depth_le

theorem exists_request {after : BST 0 n} {key : Fin n} {slack depthBound : ℕ}
    (represented : initial.Represents params)
    (root : initial.comparison.HasRoot key.val)
    (execution : SplayExecution key.val initial.splay after)
    (neighbors : HasRelevantNeighborRankBound (Snapshot.ofTree initial.comparison) slack)
    (valueBound : Analysis.contractedGap (2 * (Snapshot.ofTree initial.comparison).maxRank + 1) ≤ params.valueBound) :
    Nonempty (ArticleChronologicalExecution params initial initial.comparison after [key] 0
      (articleRequestBirthBudget slack) (articleFullComparisonBirthBudget depthBound)) := by
  let transcript := splayExecutionTranscriptWitness execution
  obtain ⟨request⟩ := ArticleCompleteRequest.exists_of_transcript root transcript.transcript represented valueBound
  let step : ArticleMacro params initial ⟨initial.comparison, after, request.final⟩ :=
    .request represented root execution transcript request
  refine ⟨{
    final := request.final
    history := .next step (.done _ request.represents)
    requests_eq := rfl
    rotations_eq := rfl
    budget := ?_
  }⟩
  simpa only [ArticleMacroHistory.birthBudget, step, ArticleMacro.birthBudget, Nat.add_zero,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_zero, Nat.mul_one] using request.birthBudget_le root neighbors

/-- Execute every actual splay in a same-comparison request group. -/
theorem exists_splaySequence {comparison before after : BST 0 n} {accesses : List (Fin n)} {slack depthBound : ℕ}
    (sequence : SplaySequence accesses before after)
    (roots : ∀ key ∈ accesses, comparison.HasRoot key.val)
    (neighbors : HasRelevantNeighborRankBound (Snapshot.ofTree comparison) slack)
    (valueBound : Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound)
    {state : Lazy.State n} (represented : state.Represents params (Snapshot.ofTree comparison).withTruePriority before) :
    Nonempty (ArticleChronologicalExecution params ⟨comparison, before, state⟩ comparison after accesses 0
      (articleRequestBirthBudget slack) (articleFullComparisonBirthBudget depthBound)) := by
  induction sequence generalizing state with
  | done tree => exact ⟨done represented⟩
  | @next key accesses before middle after head tail ih =>
      obtain ⟨first⟩ := exists_request (initial := ⟨comparison, before, state⟩) (depthBound := depthBound)
        represented (roots key (by simp)) head neighbors valueBound
      obtain ⟨rest⟩ := ih (fun key member => roots key (by simp [member])) first.represents
      exact ⟨first.append rest⟩

/-- Follow the exact indexed rotation segment, so every local depth bound
comes from the given comparison trace rather than an endpoint-only witness. -/
theorem exists_comparisonSegment {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) {depthBound slack : ℕ}
    (depths : ∀ step, trace.rotationDepth step ≤ depthBound)
    (start steps : ℕ) (within : start + steps ≤ trace.rotationCount)
    (splay : BST 0 n) {state : Lazy.State n}
    (represented : state.Represents params
      (Snapshot.ofTree (trace.state ⟨start, by omega⟩)).withTruePriority splay) :
    Nonempty (ArticleChronologicalExecution params ⟨trace.state ⟨start, by omega⟩, splay, state⟩
      (trace.state ⟨start + steps, by omega⟩) splay [] steps
      (articleRequestBirthBudget slack) (articleFullComparisonBirthBudget depthBound)) := by
  induction steps generalizing start state with
  | zero => exact ⟨done represented⟩
  | succ steps ih =>
      let index : Fin trace.rotationCount := ⟨start, by omega⟩
      obtain ⟨first⟩ := exists_rotation (initial := ⟨trace.state index.castSucc, splay, state⟩)
        (slack := slack) represented (trace.rotates index) (depths index)
      obtain ⟨rest⟩ := ih (start + 1) (by omega) first.represents
      have result := first.append rest
      exact ⟨by simpa only [index, Fin.castSucc_mk, List.nil_append, Nat.add_comm 1 steps, Nat.add_assoc] using result⟩

theorem exists_comparisonBetween {accesses : List (Fin n)}
    (trace : ComparisonTrace n accesses) {depthBound slack : ℕ}
    (depths : ∀ step, trace.rotationDepth step ≤ depthBound)
    (start finish : Fin (trace.rotationCount + 1)) (ordered : start ≤ finish)
    (splay : BST 0 n) {state : Lazy.State n}
    (represented : state.Represents params (Snapshot.ofTree (trace.state start)).withTruePriority splay) :
    Nonempty (ArticleChronologicalExecution params ⟨trace.state start, splay, state⟩ (trace.state finish) splay []
      (finish.val - start.val) (articleRequestBirthBudget slack) (articleFullComparisonBirthBudget depthBound)) := by
  have within : start.val + (finish.val - start.val) ≤ trace.rotationCount := by omega
  have endpoint : (⟨start.val + (finish.val - start.val), by omega⟩ : Fin (trace.rotationCount + 1)) = finish := by
    apply Fin.ext
    change start.val + (finish.val - start.val) = finish.val
    omega
  simpa only [endpoint] using exists_comparisonSegment trace (slack := slack) depths
    start.val (finish.val - start.val) within splay represented

/-- Every structural schedule has a complete rich realization under fixed
doubled priorities, with exactly its requests and comparison rotations. -/
theorem exists_schedule {accesses : List (Fin n)} {trace : ComparisonTrace n accesses}
    {bounds : StructuralBounds} (normal : IsStructurallyNormal bounds trace)
    (valueBound : ∀ time, Analysis.contractedGap (2 * (Snapshot.ofTree (trace.state time)).maxRank + 1) ≤ params.valueBound)
    {groups : List (ComparisonTrace.RequestGroup trace)} {time : Fin (trace.rotationCount + 1)}
    {before after : BST 0 n} (schedule : ComparisonTrace.Schedule trace groups time before after)
    {state : Lazy.State n} (represented : state.Represents params (Snapshot.ofTree (trace.state time)).withTruePriority before) :
    Nonempty (ArticleChronologicalExecution params ⟨trace.state time, before, state⟩ trace.finalTree after
      schedule.servedRequests (trace.rotationCount - time.val)
      (articleRequestBirthBudget bounds.neighborDepthSlack) (articleFullComparisonBirthBudget bounds.maxRotationDepth)) := by
  induction schedule generalizing state with
  | @finish time tree comparison =>
      exact exists_comparisonBetween trace normal.rotationDepth_le time (Fin.last trace.rotationCount)
        (Fin.le_last time) tree represented
  | @next group groups time before middle after ordered comparison splay tail ih =>
      obtain ⟨rotated⟩ := exists_comparisonBetween trace (slack := bounds.neighborDepthSlack)
        normal.rotationDepth_le time group.time ordered before represented
      obtain ⟨requested⟩ := exists_splaySequence (depthBound := bounds.maxRotationDepth) splay
        (fun key member => group.serves member) (normal.state_neighborRankBound group.time)
        (valueBound group.time) rotated.represents
      obtain ⟨rest⟩ := ih requested.represents
      have count : (group.time.val - time.val + 0) + (trace.rotationCount - group.time.val) = trace.rotationCount - time.val := by omega
      have result := (rotated.append requested).append rest
      exact ⟨by simpa only [List.nil_append, count, ComparisonTrace.Schedule.servedRequests, List.flatMap_cons] using result⟩

end ArticleChronologicalExecution
end Splay.Accounting
