import Splay.Accounting.ArticleRestorationComplete

namespace Splay.Accounting

open Splay.Rank Splay.Tree.BST Splay.Lazy

/-- The entire article request, from fixed true priorities to fixed true
priorities, retaining its actual internal and boundary pairing witnesses. -/
structure ArticleCompleteRequest {n : ℕ} (params : Interface.Parameters)
    (comparison before after : BST 0 n) (key : Fin n) (kinds : List SplayStepKind)
    (initial : Lazy.State n) where
  stage : ArticleTemporaryTransferStage params (Snapshot.ofTree comparison) before key kinds initial
  restoration : ArticleCanonicalRankChange params (stage.canonicalFinal after)
    (Snapshot.ofTree comparison).withTruePriority after
    (articleRestorationBirthBudget stage.restorationJunctionBound)

namespace ArticleCompleteRequest

variable {n : ℕ} {params : Interface.Parameters} {comparison before after : BST 0 n}
  {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (request : ArticleCompleteRequest params comparison before after key kinds initial)

noncomputable def events : List (Event n) := (request.stage.events ++ [.silent]) ++ request.restoration.events

noncomputable def final : Lazy.State n := request.restoration.final

theorem trace (comparisonRoot : comparison.HasRoot key.val)
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    Trace params initial request.events request.final :=
  (request.stage.canonical_trace comparisonRoot transcript).append request.restoration.trace

theorem represents : request.final.Represents params (Snapshot.ofTree comparison).withTruePriority after :=
  request.restoration.represents

theorem births : request.final.blocks.length ≤ initial.blocks.length +
    32 + articleRestorationBirthBudget request.stage.restorationJunctionBound := by
  have stageBound := request.stage.canonical_births after
  have suffixBound := request.restoration.births
  change request.restoration.final.blocks.length ≤ _
  omega

theorem erased_events : eraseOperations request.events = eraseOperations request.stage.events ++
    eraseOperations request.restoration.events := by
  rw [events, eraseOperations_append, request.stage.canonical_erased_events]

theorem inserts : Interface.totalInserts (eraseOperations request.events) = 2 * request.stage.pairing.boundaryCount := by
  rw [request.erased_events, Interface.totalInserts_append, request.restoration.noInserts, Nat.add_zero]
  exact request.stage.inserts

theorem increases : Interface.totalIncreases (eraseOperations request.events) ≤
    request.stage.pairing.internal.chain.goodCount + 8 * params.valueBound * request.stage.pairing.boundaryCount := by
  rw [request.erased_events, Interface.totalIncreases_append, request.restoration.noIncreases, Nat.add_zero]
  exact request.stage.increases

theorem gap_pays_good (comparisonRoot : comparison.HasRoot key.val)
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag) :
    geometricGapPotential request.final + request.stage.pairing.internal.chain.goodCount ≤
      geometricGapPotential initial + 8 * params.valueBound * request.stage.pairing.boundaryCount := by
  have prefixDrop := request.stage.canonical_gap_pays_good comparisonRoot transcript
  have suffixDrop := request.restoration.gap_le (request.stage.canonical_represents comparisonRoot transcript).stable
  change geometricGapPotential request.restoration.final + _ ≤ _
  omega

theorem zigZigs_le_activity_add_inserts :
    2 * kinds.count .zigZig ≤ Interface.totalActivity (eraseOperations request.events) +
      Interface.totalInserts (eraseOperations request.events) := by
  have prefixBound := request.stage.zigZigs_le_activity_add_inserts
  rw [request.erased_events, Interface.totalActivity_append, Interface.totalInserts_append,
    request.restoration.noInserts, Nat.add_zero]
  omega

/-- No geometric certificate is an input: the represented starting state,
actual splay transcript, comparison root and fixed value cap construct the
complete request including the canonical true-priority endpoint. -/
theorem exists_of_transcript (comparisonRoot : comparison.HasRoot key.val)
    {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (represented : initial.Represents params (Snapshot.ofTree comparison).withTruePriority before)
    (valueBound : Analysis.contractedGap (2 * (Snapshot.ofTree comparison).maxRank + 1) ≤ params.valueBound) :
    Nonempty (ArticleCompleteRequest params comparison before after key kinds initial) := by
  obtain ⟨stage, _, _⟩ := ArticleTemporaryTransferStage.exists_canonicalPrefix comparisonRoot transcript represented valueBound
  obtain ⟨restoration⟩ := stage.exists_restoration comparisonRoot transcript
  exact ⟨⟨stage, restoration⟩⟩

end ArticleCompleteRequest
end Splay.Accounting
