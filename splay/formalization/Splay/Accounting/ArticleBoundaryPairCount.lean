import Splay.Accounting.ArticleBoundarySourceCount
import Splay.Accounting.ArticlePairingStage

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

private theorem filter_length_le_of_forall₂ {α β : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β} (aligned : List.Forall₂ relation left right)
    (leftKeep : α → Bool) (rightKeep : β → Bool)
    (implies : ∀ a b, relation a b → rightKeep b = true → leftKeep a = true) :
    (right.filter rightKeep).length ≤ (left.filter leftKeep).length := by
  induction aligned with
  | nil => simp
  | @cons a b left right related rest ih =>
    simp only [List.filter_cons]
    by_cases rightSelected : rightKeep b = true
    · rw [if_pos rightSelected, if_pos (implies a b related rightSelected)]
      simpa using Nat.add_le_add_right ih 1
    · rw [if_neg rightSelected]
      split <;> simp_all <;> omega

/-- In each phase, every loser in a source comes from a distinct row which
touches that source. This uses the literal endpoint correspondence. -/
theorem ArticleBatchEndpointAgreement.losers_in_source_le_rows_touching {n lower upper key : ℕ}
    {snapshot : Snapshot n} {before : BST lower upper} {bound : upper ≤ n} {groups : List ℕ}
    {phase : PairingPhase} {batches : ArticleRetainedPairingBatches snapshot before bound key groups}
    {matching : List (Interface.Pairing n)} (agreement : ArticleBatchEndpointAgreement phase batches matching)
    (elements : List (Element n)) :
    (matching.filter (fun pairing => decide (pairing.loser ∈ elements))).length ≤
      (articleRowsTouching batches.rows elements).length := by
  apply filter_length_le_of_forall₂ agreement
  intro row pairing equal selected
  apply decide_eq_true
  refine ⟨pairing.loser, ?_, of_decide_eq_true selected⟩
  have member : pairing.loser ∈ articleRowSelection phase row := by rw [equal]; simp
  cases phase with
  | first => exact List.mem_append_left _ member
  | second => exact List.mem_append_right _ member

/-- The two actually executed boundary phases remove at most four losers
from any admissible prepared source during one request. -/
theorem ArticlePairingStage.boundary_losers_in_source_le_four {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before after : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    {kinds : List SplayStepKind} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (stage : ArticlePairingStage params snapshot before key kinds initial)
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    {id : Interface.BlockId} {source : Block n} (found : stage.preparation.final.blocks[id]? = some source)
    (owner : source.owner = valuePos key) (notLeft : id ≠ stage.preparation.leftId) (notRight : id ≠ stage.preparation.rightId)
    (nonempty : source.elements ≠ [])
    (admissible : stage.preparation.SourceAdmissible stage.allBatches ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩) :
    ((stage.boundary.firstAllocation.matching ++ stage.boundary.secondAllocation.matching).filter
      (fun pairing => decide (pairing.loser ∈ source.elements))).length ≤ 4 := by
  have rows := stage.preparation.boundaryRows_touching_source_le_two transcript stage.rankZero stage.allBatches
    found owner notLeft notRight nonempty admissible
  have first := stage.boundary.firstAllocation.agreement.losers_in_source_le_rows_touching source.elements
  have second := stage.boundary.secondAllocation.agreement.losers_in_source_le_rows_touching source.elements
  rw [List.filter_append, List.length_append]
  omega

end Splay.Accounting
