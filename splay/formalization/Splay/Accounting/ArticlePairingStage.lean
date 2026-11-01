import Splay.Accounting.ArticleBoundaryPhases

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- The complete preparation/internal/boundary pairing stage of one request.
Transfers of the surviving root-child intervals follow this stage. -/
structure ArticlePairingStage {n : ℕ} (params : Interface.Parameters)
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n)
    (kinds : List SplayStepKind) (initial : Lazy.State n) where
  rankZero : snapshot.rank (valuePos key) = 0
  allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val
    (zigZigDoubleGroupIndices kinds 0)
  ordered : allBatches.Ordered
  preparation : ArticleRequestPreparation params snapshot before key initial
  internal : ArticleAdmissibleWorklistExecution
    (preparation.admissibleWorklist allBatches (zigZigDoubleGroupIndices_nodup kinds 0) rankZero)
  boundary : ArticleBoundaryPhasesExecution params internal.chain.final
    (preparation.boundaryBatches allBatches (zigZigDoubleGroupIndices_nodup kinds 0) rankZero)

namespace ArticlePairingStage

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticlePairingStage params snapshot before key kinds initial)

noncomputable def events : List (Event n) := stage.preparation.events ++ stage.internal.chain.events ++ stage.boundary.events

noncomputable def final : Lazy.State n := stage.boundary.final

noncomputable def boundaryCount : ℕ :=
  (stage.preparation.boundaryBatches stage.allBatches (zigZigDoubleGroupIndices_nodup kinds 0) stage.rankZero).rows.length

theorem trace : Trace params initial stage.events stage.final :=
  (stage.preparation.trace.append stage.internal.chain.trace).append stage.boundary.trace

theorem stable : stage.final.Stable params := stage.boundary.stable

theorem births : stage.final.blocks.length ≤ initial.blocks.length + 16 := by
  change stage.boundary.final.blocks.length ≤ _
  rw [stage.boundary.blocks_length_eq, stage.internal.chain.blocks_length_eq]
  exact stage.preparation.births

theorem inserts : Interface.totalInserts (eraseOperations stage.events) = 2 * stage.boundaryCount := by
  simp only [events, eraseOperations_append, Interface.totalInserts_append, stage.preparation.noInserts,
    stage.internal.chain.inserts_eq_zero, Nat.zero_add]
  exact stage.boundary.inserts

theorem increases : Interface.totalIncreases (eraseOperations stage.events) ≤
    stage.internal.chain.goodCount + 8 * params.valueBound * stage.boundaryCount := by
  simp only [events, eraseOperations_append, Interface.totalIncreases_append, stage.preparation.noIncreases,
    stage.internal.chain.increases_eq_good, Nat.zero_add]
  exact Nat.add_le_add_left stage.boundary.increases _

/-- Internal good pairings are paid by genuine geometric loss. Boundary
normalization is the only source of potential growth in the complete stage. -/
theorem gap_pays_good : geometricGapPotential stage.final + stage.internal.chain.goodCount ≤
    geometricGapPotential initial + 8 * params.valueBound * stage.boundaryCount := by
  have balance := stage.boundary.trace.toInterface.totalValue_balance
  have internalStable := stage.internal.chain.finalStable
  rw [← geometricGapPotential_eq internalStable.2.1 internalStable.2.2.2.2.2,
    ← geometricGapPotential_eq stage.boundary.stable.2.1 stage.boundary.stable.2.2.2.2.2] at balance
  have internalDrop := stage.internal.chain.gap_drop
  have preparationDrop := stage.preparation.gap_le
  have cost := stage.boundary.increases
  change Interface.totalIncreases (eraseOperations stage.boundary.events) ≤
    8 * params.valueBound * stage.boundaryCount at cost
  change geometricGapPotential stage.boundary.final + _ ≤ _
  omega

/-- Every actual transcript supplies the entire pairing stage; no ready list,
source allocation or boundary-order certificate is required from the caller. -/
theorem exists_of_transcript {after : BST 0 n} {execution : SplayExecution key.val before after}
    {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (represented : initial.Represents params snapshot before)
    (valueBound : Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Nonempty (ArticlePairingStage params snapshot before key kinds initial) := by
  obtain ⟨allBatches, ordered⟩ := ArticleRetainedPairingBatches.exists_ordered_of_groups transcript
    (zigZigDoubleGroupIndices kinds 0) (zigZigDoubleGroupIndices_nodup kinds 0)
    (fun _ member => member) key.isLt rankZero
  obtain ⟨preparation⟩ := ArticleRequestPreparation.exists_preparation snapshot before key rankZero represented
  obtain ⟨internal⟩ := preparation.exists_admissibleWorklistExecution allBatches
    (zigZigDoubleGroupIndices_nodup kinds 0) rankZero
  obtain ⟨boundary⟩ := preparation.exists_boundaryPhases allBatches
    (zigZigDoubleGroupIndices_nodup kinds 0) rankZero ordered valueBound internal
  exact ⟨⟨rankZero, allBatches, ordered, preparation, internal, boundary⟩⟩

end ArticlePairingStage
end Splay.Accounting
