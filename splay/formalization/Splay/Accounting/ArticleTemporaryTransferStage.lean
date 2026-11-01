import Splay.Accounting.ArticleTemporaryBoundaryRanks
import Splay.Accounting.ArticlePairingStageTransfers
import Splay.Accounting.ArticlePairingStageCounts

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- A concrete article request prefix through both whole-side transfers.
Canonical identification with the final splay tree and restoration of the
true boundary ranks follow this prefix. -/
structure ArticleTemporaryTransferStage {n : ℕ} (params : Interface.Parameters)
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n)
    (kinds : List SplayStepKind) (initial : Lazy.State n) where
  setup : ArticleTemporaryPreparation params snapshot before key initial
  pairing : ArticlePairingStage params setup.temporarySnapshot before key kinds setup.final
  leftGeometry : SideTransferGeometry pairing.final.view (valuePos key)
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection setup.temporarySnapshot before key).left .left
  rightGeometry : SideTransferGeometry pairing.final.view (valuePos key)
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection setup.temporarySnapshot before key).right .right

namespace ArticleTemporaryTransferStage

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticleTemporaryTransferStage params snapshot before key kinds initial)

noncomputable def final : Lazy.State n :=
  stage.pairing.final.transferBothSides stage.leftGeometry stage.rightGeometry stage.pairing.stable.2.2.1

noncomputable def events : List (Event n) := stage.setup.events ++ stage.pairing.events ++ [.silent, .silent]

theorem transferTrace_stable : Trace params stage.pairing.final [.silent, .silent] stage.final ∧
    stage.final.Stable params := by
  have leftReady := stage.pairing.transferConditions .left stage.leftGeometry
  have rightReady := stage.pairing.transferConditions .right stage.rightGeometry
  exact stage.leftGeometry.transferBothSides_trace_stable stage.rightGeometry stage.pairing.stable
    leftReady.1 leftReady.2 rightReady.1 rightReady.2

theorem trace : Trace params initial stage.events stage.final :=
  (stage.setup.trace.append stage.pairing.trace).append stage.transferTrace_stable.1

theorem stable : stage.final.Stable params := stage.transferTrace_stable.2

theorem source_topDown :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection stage.setup.temporarySnapshot before key
    stage.final.view.topDown (valuePos key) .left = [selection.left] ∧
      stage.final.view.topDown (valuePos key) .right = [selection.right] :=
  stage.pairing.final.transferBothSides_source_topDown stage.leftGeometry stage.rightGeometry stage.pairing.stable.2.2.1

theorem erased_events : eraseOperations stage.events =
    eraseOperations stage.setup.events ++ eraseOperations stage.pairing.events := by
  rw [events, eraseOperations_append, eraseOperations_append,
    show eraseOperations ([.silent, .silent] : List (Event n)) = [] from rfl, List.append_nil]

theorem births : stage.final.blocks.length ≤ initial.blocks.length + 32 := by
  have setupBirths := stage.setup.births
  have pairingBirths := stage.pairing.births
  change (stage.pairing.final.transferBothSides stage.leftGeometry stage.rightGeometry stage.pairing.stable.2.2.1).blocks.length ≤ _
  rw [stage.pairing.final.transferBothSides_blocks_length stage.leftGeometry stage.rightGeometry stage.pairing.stable.2.2.1]
  omega

theorem inserts : Interface.totalInserts (eraseOperations stage.events) = 2 * stage.pairing.boundaryCount := by
  rw [stage.erased_events, Interface.totalInserts_append, stage.setup.noInserts, Nat.zero_add]
  exact stage.pairing.inserts

theorem increases : Interface.totalIncreases (eraseOperations stage.events) ≤
    stage.pairing.internal.chain.goodCount + 8 * params.valueBound * stage.pairing.boundaryCount := by
  rw [stage.erased_events, Interface.totalIncreases_append, stage.setup.noIncreases, Nat.zero_add]
  exact stage.pairing.increases

theorem transfer_gap_eq : geometricGapPotential stage.final = geometricGapPotential stage.pairing.final := by
  rw [geometricGapPotential_eq stage.stable.2.1 stage.stable.2.2.2.2.2,
    geometricGapPotential_eq stage.pairing.stable.2.1 stage.pairing.stable.2.2.2.2.2]
  rfl

theorem gap_pays_good : geometricGapPotential stage.final + stage.pairing.internal.chain.goodCount ≤
    geometricGapPotential initial + 8 * params.valueBound * stage.pairing.boundaryCount := by
  rw [stage.transfer_gap_eq]
  have preparationDrop := stage.setup.gap_le
  have pairingDrop := stage.pairing.gap_pays_good
  omega

theorem zigZigs_le_activity_add_inserts :
    2 * kinds.count .zigZig ≤ Interface.totalActivity (eraseOperations stage.events) +
      Interface.totalInserts (eraseOperations stage.events) := by
  have paid := stage.pairing.zigZigs_le_activity_add_inserts
  rw [stage.erased_events, Interface.totalActivity_append, Interface.totalInserts_append,
    stage.setup.noInserts, Nat.zero_add]
  omega

/-- The actual splay transcript supplies this entire prefix, including
artificial-rank preparation, all pairings and both real block transfers. -/
theorem exists_of_transcript {after : BST 0 n} {execution : SplayExecution key.val before after}
    {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (represented : initial.Represents params snapshot.withTruePriority before)
    (valueBound : Analysis.contractedGap (2 * snapshot.maxRank + 1) ≤ params.valueBound) :
    Nonempty (ArticleTemporaryTransferStage params snapshot before key kinds initial) := by
  obtain ⟨setup⟩ := ArticleTemporaryPreparation.exists_of_represents snapshot before key rankZero represented
  obtain ⟨pairing⟩ := ArticlePairingStage.exists_of_transcript transcript setup.temporary_rank_zero setup.represents valueBound
  obtain ⟨leftGeometry⟩ := pairing.exists_sideTransferGeometry .left (setup.boundary_rank_lt .left)
  obtain ⟨rightGeometry⟩ := pairing.exists_sideTransferGeometry .right (setup.boundary_rank_lt .right)
  exact ⟨⟨setup, pairing, leftGeometry, rightGeometry⟩⟩

end ArticleTemporaryTransferStage
end Splay.Accounting
