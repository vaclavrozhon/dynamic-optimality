import Splay.Accounting.ArticlePairingStageGeometry

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST

/-- Count the genuine source `pass` activity in the same chain trace. -/
theorem ArticleSourceMacroChain.activity_eq_matchingLength {n : ℕ}
    {params : Interface.Parameters} {initial : Lazy.State n}
    (chain : ArticleSourceMacroChain params initial) :
    Interface.totalActivity (eraseOperations chain.events) = chain.matching.length := by
  induction chain with
  | nil => rfl
  | cons head tail ih =>
      change Interface.totalActivity (eraseOperations (head.events ++ tail.events)) =
        ((head.batch.firstMatching ++ head.batch.secondMatching) ++ tail.matching).length
      rw [eraseOperations_append, Interface.totalActivity_append, head.activity_eq_pairings,
        ih, List.length_append]
      simp only [List.length_append]

/-- Two complete internal passes execute the two phase selections of each
frozen internal row. -/
theorem ArticleAdmissibleWorklistExecution.activity_eq_rows
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {params : Interface.Parameters}
    {state : Lazy.State n} {items : List (ArticleAdmissibleSourceWorkItem key snapshot before params state)}
    (execution : ArticleAdmissibleWorklistExecution items) :
    Interface.totalActivity (eraseOperations execution.chain.events) =
      2 * (items.flatMap fun item => item.batches.rows).length := by
  rw [execution.chain.activity_eq_matchingLength]
  have count : ∀ {batches : List (ArticleSourceLoserBatch n)}
      {rows : List (List (ℕ × (List (External n) × List (External n))))},
      List.Forall₂ (fun batch rows =>
        List.Forall₂ (fun row pairing => row.2.1 = [pairing.winner, pairing.loser]) rows batch.firstMatching ∧
        List.Forall₂ (fun row pairing => row.2.2 = [pairing.winner, pairing.loser]) rows batch.secondMatching) batches rows →
      (batches.flatMap fun batch => batch.firstMatching ++ batch.secondMatching).length = 2 * rows.flatten.length := by
    intro batches rows agreement
    induction agreement with
    | nil => rfl
    | @cons batch row batches rows related rest ih =>
        simp only [List.flatMap_cons, List.flatten_cons, List.length_append]
        rw [← related.1.length_eq, ← related.2.length_eq, ih]
        omega
  exact count execution.batchRowsAgreement

/-- The exact boundary complement and the selected internal rows cover all
original rows, even without assuming a separate enumeration cardinality law. -/
theorem ArticleRequestPreparation.rows_length_le_internal_add_boundary
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    {groups : List ℕ}
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0) :
    allBatches.rows.length ≤ (preparation.internalRows allBatches distinct rankZero).length +
      (preparation.boundaryBatches allBatches distinct rankZero).rows.length := by
  classical
  let internalRows := preparation.internalRows allBatches distinct rankZero
  let selected := allBatches.rows.filter fun row => decide (row ∈ internalRows)
  have rowsNodup : allBatches.rows.Nodup := (allBatches.groups_perm.nodup_iff.mpr distinct).of_map
  have selectedNodup : selected.Nodup := rowsNodup.filter _
  have selectedLe : selected.length ≤ internalRows.length := by
    calc
      selected.length = selected.toFinset.card := (List.toFinset_card_of_nodup selectedNodup).symm
      _ ≤ internalRows.toFinset.card := Finset.card_le_card (by
        intro row member
        exact List.mem_toFinset.mpr (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp member)).2))
      _ ≤ internalRows.length := List.toFinset_card_le internalRows
  have partition := List.length_eq_length_filter_add (l := allBatches.rows)
    (fun row => decide (row ∈ internalRows))
  have count : allBatches.rows.length = selected.length +
      (preparation.boundaryBatches allBatches distinct rankZero).rows.length := by
    simpa [selected, internalRows, ArticleRequestPreparation.boundaryBatches,
      ArticleRetainedPairingBatches.filter] using partition
  change allBatches.rows.length ≤ internalRows.length + _
  omega

/-- Group enumeration has exactly one entry per zig-zig. -/
theorem zigZigDoubleGroupIndices_length (kinds : List SplayStepKind) (start : ℕ) :
    (zigZigDoubleGroupIndices kinds start).length = kinds.count .zigZig := by
  induction kinds generalizing start with
  | nil => rfl
  | cons kind kinds ih => cases kind <;> simp [zigZigDoubleGroupIndices, ih]

/-- The actual pairing-stage trace pays for all original zig-zigs by passes
and boundary inserts, without a caller-supplied pairing classification. -/
theorem ArticlePairingStage.zigZigs_le_activity_add_inserts
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (stage : ArticlePairingStage params snapshot before key kinds initial) :
    2 * kinds.count .zigZig ≤ Interface.totalActivity (eraseOperations stage.events) +
      Interface.totalInserts (eraseOperations stage.events) := by
  have rowsLe := stage.preparation.rows_length_le_internal_add_boundary stage.allBatches
    (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero
  have allLength := stage.allBatches.length_eq_eligibleGroups_length
  rw [zigZigDoubleGroupIndices_length] at allLength
  have internalActivity := stage.internal.activity_eq_rows
  change Interface.totalActivity (eraseOperations stage.internal.chain.events) =
    2 * (stage.preparation.internalRows stage.allBatches (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero).length
    at internalActivity
  have inserts := stage.inserts
  change Interface.totalInserts (eraseOperations stage.events) = 2 *
    (stage.preparation.boundaryBatches stage.allBatches (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero).rows.length
    at inserts
  have activityLe : Interface.totalActivity (eraseOperations stage.internal.chain.events) ≤
      Interface.totalActivity (eraseOperations stage.events) := by
    simp only [ArticlePairingStage.events, eraseOperations_append, Interface.totalActivity_append]
    omega
  omega

end Splay.Accounting
