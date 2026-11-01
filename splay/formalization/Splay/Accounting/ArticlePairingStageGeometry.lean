import Splay.Accounting.ArticlePairingStage

namespace Splay.Accounting.ArticlePairingStage

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open ArticleBatchDestinationAllocation

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticlePairingStage params snapshot before key kinds initial)

/-- All genuinely executed pairings, retaining their actual growing IDs. -/
noncomputable def matching : List (Interface.Pairing n) :=
  stage.internal.chain.matching ++
    (stage.boundary.firstAllocation.matching ++ stage.boundary.secondAllocation.matching)

/-- Boundary losers are disjoint from every already executed internal loser. -/
theorem internal_boundary_losers_ne : ∀ earlier ∈ stage.internal.chain.matching,
    ∀ later ∈ stage.boundary.firstAllocation.matching ++ stage.boundary.secondAllocation.matching,
      earlier.loser ≠ later.loser := by
  intro earlier earlierMember later laterMember equal
  have inInternal : later.loser ∈ stage.internal.chain.matching.flatMap (fun p => [p.winner, p.loser]) :=
    List.mem_flatMap.mpr ⟨earlier, earlierMember, by simp [equal]⟩
  rcases List.mem_append.mp laterMember with first | second
  · exact (stage.preparation.boundaryPair_not_internal stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero stage.internal
      stage.boundary.firstAllocation.agreement first).2 inInternal
  · exact (stage.preparation.boundaryPair_not_internal stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero stage.internal
      stage.boundary.secondAllocation.agreement second).2 inInternal

/-- The actual final heap reparents exactly the selected losers; ranks,
root and all other parent/side data are retained. -/
theorem exists_reparented : ∃ afterView : BatchReparentedView stage.preparation.final.view stage.matching,
    afterView.view = stage.final.view := by
  have payloads : stage.internal.chain.batches.Pairwise
      (Function.onFun List.Disjoint ArticleSourceLoserBatch.sourceElements) := by
    have mapped : (stage.internal.chain.batches.map ArticleSourceLoserBatch.sourceElements).Pairwise List.Disjoint := by
      rw [stage.internal.batchSourceElements_eq]
      exact stage.preparation.admissibleWorklist_payloads_disjoint stage.allBatches
        (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero
    exact (List.pairwise_map (f := ArticleSourceLoserBatch.sourceElements)).mp mapped
  obtain ⟨internalView, internalViewEq⟩ := stage.internal.chain.view_reparented payloads
  have boundaryDistinct := stage.allBatches.filtered_groups_nodup (zigZigDoubleGroupIndices_nodup kinds 0)
    (fun row => decide (row ∉ stage.preparation.internalRows stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero))
  let boundaryView := (stage.boundary.reparented boundaryDistinct).transportSource internalViewEq
  exact ⟨internalView.append boundaryView stage.internal_boundary_losers_ne,
    stage.boundary.reparented_view boundaryDistinct⟩

/-- Every original zig-zig row has both phase pairs in the actual executed
matching, whether assigned to an internal source or to the boundary complement. -/
theorem rows_complete
    {row : ℕ × (List (External n) × List (External n))}
    (member : row ∈ stage.allBatches.rows) (phase : PairingPhase) :
    ∃ pairing ∈ stage.matching, articleRowSelection phase row = [pairing.winner, pairing.loser] := by
  by_cases internal : row ∈ stage.preparation.internalRows stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero
  · obtain ⟨item, itemMember, rowMember⟩ := List.mem_flatMap.mp internal
    have rowsMember : item.batches.rows ∈ (stage.preparation.admissibleWorklist stage.allBatches
        (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero).map (fun item => item.batches.rows) :=
      List.mem_map.mpr ⟨item, itemMember, rfl⟩
    obtain ⟨batch, batchMember, firstAgreement, secondAgreement⟩ :=
      forall₂_exists_right_of_mem_left stage.internal.batchRowsAgreement.flip rowsMember
    cases phase with
    | first =>
        obtain ⟨pairing, pairingMember, equal⟩ := forall₂_exists_right_of_mem_left firstAgreement rowMember
        exact ⟨pairing, List.mem_append_left _
          (List.mem_flatMap.mpr ⟨batch, batchMember, List.mem_append_left _ pairingMember⟩), equal⟩
    | second =>
        obtain ⟨pairing, pairingMember, equal⟩ := forall₂_exists_right_of_mem_left secondAgreement rowMember
        exact ⟨pairing, List.mem_append_left _
          (List.mem_flatMap.mpr ⟨batch, batchMember, List.mem_append_right _ pairingMember⟩), equal⟩
  · have boundary := (stage.preparation.mem_boundaryBatches stage.allBatches
      (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero row).mpr ⟨member, internal⟩
    cases phase with
    | first =>
        obtain ⟨pairing, pairingMember, equal⟩ := forall₂_exists_right_of_mem_left
          stage.boundary.firstAllocation.agreement boundary
        exact ⟨pairing, List.mem_append_right _ (List.mem_append_left _ pairingMember), equal⟩
    | second =>
        obtain ⟨pairing, pairingMember, equal⟩ := forall₂_exists_right_of_mem_left
          stage.boundary.secondAllocation.agreement boundary
        exact ⟨pairing, List.mem_append_right _ (List.mem_append_right _ pairingMember), equal⟩

/-- Conversely, every executed pairing is one of the two genuine selections
of an original zig-zig row. -/
theorem rows_sound {pairing : Interface.Pairing n} (member : pairing ∈ stage.matching) :
    ∃ row ∈ stage.allBatches.rows, ∃ phase : PairingPhase,
      articleRowSelection phase row = [pairing.winner, pairing.loser] := by
  rcases List.mem_append.mp member with internal | boundary
  · obtain ⟨batch, batchMember, pairingMember⟩ := List.mem_flatMap.mp internal
    obtain ⟨rows, rowsMember, firstAgreement, secondAgreement⟩ :=
      forall₂_exists_right_of_mem_left stage.internal.batchRowsAgreement batchMember
    obtain ⟨item, itemMember, rowsEq⟩ := List.mem_map.mp rowsMember
    have rowOriginal : ∀ row ∈ rows, row ∈ stage.allBatches.rows := by
      intro row rowMember
      apply stage.preparation.internalRows_subset stage.allBatches (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero
      exact List.mem_flatMap.mpr ⟨item, itemMember, by simpa [rowsEq] using rowMember⟩
    rcases List.mem_append.mp pairingMember with first | second
    · obtain ⟨row, rowMember, equal⟩ := forall₂_exists_right_of_mem_left firstAgreement.flip first
      exact ⟨row, rowOriginal row rowMember, .first, equal⟩
    · obtain ⟨row, rowMember, equal⟩ := forall₂_exists_right_of_mem_left secondAgreement.flip second
      exact ⟨row, rowOriginal row rowMember, .second, equal⟩
  · have rowOriginal : ∀ row ∈ (stage.preparation.boundaryBatches stage.allBatches
          (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero).rows, row ∈ stage.allBatches.rows := by
      intro row rowMember
      exact ((stage.preparation.mem_boundaryBatches stage.allBatches
        (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero row).mp rowMember).1
    rcases List.mem_append.mp boundary with first | second
    · obtain ⟨row, rowMember, equal⟩ := stage.boundary.firstAllocation.agreement.exists_row_of_mem first
      exact ⟨row, rowOriginal row rowMember, .first, equal⟩
    · obtain ⟨row, rowMember, equal⟩ := stage.boundary.secondAllocation.agreement.exists_row_of_mem second
      exact ⟨row, rowOriginal row rowMember, .second, equal⟩

end Splay.Accounting.ArticlePairingStage
