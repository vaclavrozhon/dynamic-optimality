import Splay.Accounting.ArticlePairingBoundaryCredit

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

namespace ArticlePairingStage

variable {n cutoff : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before after : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
  (stage : ArticlePairingStage params snapshot before key kinds initial)
  (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
  (exempt : params.exemptPasses = 2) (numerator : params.matchingNumerator = 1)
  (denominator : params.matchingDenominator = 8)

include transcript exempt numerator denominator

theorem workItem_boundary_estimate
    {item : ArticleAdmissibleSourceWorkItem key.val snapshot before params stage.preparation.final}
    (member : item ∈ stage.preparation.admissibleWorklist stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero) :
    cutoff * (stage.boundaryMatching.filter fun pairing => decide (pairing.loser ∈ item.source.elements)).length ≤
      4 * cutoff * boundarySourceDemand cutoff item.source item.batches.rows.length +
        32 * item.batches.rows.length := by
  by_cases empty : item.source.elements = []
  · simp [empty]
  obtain ⟨owner, notLeft, notRight, admissible⟩ := stage.workItem_spec member
  have atMostFour := stage.boundary_losers_in_source_le_four transcript item.sourceFound
    owner notLeft notRight empty admissible
  apply boundarySourceDemand_pays atMostFour (fun _ => List.length_pos_iff.mpr empty)
  rcases item.admissible with first | fraction
  · left
    rw [exempt] at first
    omega
  · right
    have rows := item.batches.length_eq_eligibleGroups_length
    simpa only [numerator, denominator, Nat.one_mul, ← rows] using fraction

/-- All actual boundary pairs are paid by either lifetime credit or actual
internal activity. The cutoff is arbitrary, so the global proof can choose
it after fixing the uniform constants of the interface theorem. -/
theorem boundary_credit_estimate
    (unbroken : PassedBlocksUnbroken snapshot before stage.preparation.final) :
    cutoff * (2 * stage.boundaryCount) +
      4 * cutoff * Interface.boundaryCredit cutoff stage.final.toInterface ≤
        4 * cutoff * Interface.boundaryCredit cutoff initial.toInterface +
          64 * cutoff * Interface.boundaryCreditCapacity cutoff +
            16 * Interface.totalActivity (eraseOperations stage.events) := by
  classical
  let items := stage.preparation.admissibleWorklist stage.allBatches
    (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero
  let smallCount := (stage.boundaryMatching.filter fun pairing => stage.preparedSmall pairing.loser).length
  let demands := (items.map fun item => boundarySourceDemand cutoff item.source item.batches.rows.length).sum
  let rows := (items.map fun item => item.batches.rows.length).sum
  let counts := (items.map fun item => (stage.boundaryMatching.filter
    fun pairing => decide (pairing.loser ∈ item.source.elements)).length).sum
  have cover : stage.boundaryMatching.length ≤ smallCount + counts := by
    apply length_le_filter_add_sum_filters
    intro pairing member
    rcases stage.boundary_small_or_workItem transcript (by omega) (by omega) unbroken member with
      small | ⟨item, itemMember, inside⟩
    · exact Or.inl small
    · exact Or.inr ⟨item, itemMember, decide_eq_true inside⟩
  have sumPaid : cutoff * counts ≤ 4 * cutoff * demands + 32 * rows := by
    have summed := List.sum_le_sum (fun item (member : item ∈ items) =>
      stage.workItem_boundary_estimate (cutoff := cutoff) transcript exempt numerator denominator member)
    simpa only [List.sum_map_add, List.sum_map_mul_left] using summed
  have internalPaid := stage.internal.boundaryCredit_drop (cutoff := cutoff)
  have smallPaid := stage.smallCredit (cutoff := cutoff)
  change Interface.boundaryCredit cutoff stage.internal.chain.final.toInterface + demands ≤
    Interface.boundaryCredit cutoff stage.preparation.final.toInterface at internalPaid
  have creditPaid : Interface.boundaryCredit cutoff stage.final.toInterface + smallCount + demands ≤
      Interface.boundaryCredit cutoff stage.preparation.final.toInterface := by
    omega
  have localPaid : cutoff * stage.boundaryMatching.length +
      4 * cutoff * Interface.boundaryCredit cutoff stage.final.toInterface ≤
        4 * cutoff * Interface.boundaryCredit cutoff stage.preparation.final.toInterface + 32 * rows := by
    have coverWeighted := Nat.mul_le_mul_left cutoff cover
    have creditWeighted := Nat.mul_le_mul_left (4 * cutoff) creditPaid
    nlinarith
  have setup := stage.preparation.trace.toInterface.boundaryCredit_bound (cutoff := cutoff)
  have growth := stage.preparation.trace.blocks_length_eq
  have births := stage.preparation.births
  have growthLe : Interface.totalBlockGrowth (eraseOperations stage.preparation.events) ≤ 16 := by omega
  have setupPaid : Interface.boundaryCredit cutoff stage.preparation.final.toInterface ≤
      Interface.boundaryCredit cutoff initial.toInterface + 16 * Interface.boundaryCreditCapacity cutoff := by
    nlinarith [Nat.mul_le_mul_left (Interface.boundaryCreditCapacity cutoff) growthLe]
  have setupWeighted := Nat.mul_le_mul_left (4 * cutoff) setupPaid
  have activity := stage.internal.activity_eq_rows
  have flatLength : (items.flatMap fun item => item.batches.rows).length = rows := by
    simp [rows, List.length_flatMap]
  change Interface.totalActivity (eraseOperations stage.internal.chain.events) =
    2 * (items.flatMap fun item => item.batches.rows).length at activity
  rw [flatLength] at activity
  have activityLe : Interface.totalActivity (eraseOperations stage.internal.chain.events) ≤
      Interface.totalActivity (eraseOperations stage.events) := by
    simp only [events, eraseOperations_append, Interface.totalActivity_append]
    omega
  rw [stage.boundaryMatching_length] at localPaid
  nlinarith

end ArticlePairingStage
end Splay.Accounting
