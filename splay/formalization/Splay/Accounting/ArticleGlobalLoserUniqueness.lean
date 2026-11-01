import Splay.Accounting.ArticlePairingLoserRestoration

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/-- Both endpoints of any selected phase pair belong to its source. -/
theorem ArticleSourcePairings.endpoints_mem_source
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ} {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    pairing.winner ∈ elements ∧ pairing.loser ∈ elements := by
  obtain ⟨row, rowMember, selected⟩ := agreement.exists_row_of_mem member
  have inside := plan.contained row rowMember
  cases phase with
  | first =>
      simp only [articleRowSelection] at selected
      constructor
      · exact inside _ (List.mem_append_left _ (by rw [selected]; simp))
      · exact inside _ (List.mem_append_left _ (by rw [selected]; simp))
  | second =>
      simp only [articleRowSelection] at selected
      constructor
      · exact inside _ (List.mem_append_right _ (by rw [selected]; simp))
      · exact inside _ (List.mem_append_right _ (by rw [selected]; simp))

namespace ArticleInternalPairingFractionCertificate

/-- Every loser selected by the first retained article batch belongs to the
source payload certified by the fraction theorem. -/
theorem first_loser_mem_source
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {matching : List (Interface.Pairing n)}
    (agreement :
      ArticleBatchEndpointAgreement .first batches matching)
    {pairing : Interface.Pairing n}
    (member : pairing ∈ matching) :
    pairing.loser ∈ elements := by
  obtain ⟨row, rowMember, selected⟩ :=
    agreement.exists_row_of_mem member
  obtain ⟨winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, firstAdjacent, secondAdjacent,
      losersNe, candidatePerm, candidateChunk, candidateSegment,
      firstInBlock, secondInBlock, winnerInside, firstInside,
      secondInside⟩ :=
    certificate.retainedRow_inside batches rowMember
  simp only [articleRowSelection] at selected
  have pairEq : [winner, firstLoser] =
      [pairing.winner, pairing.loser] :=
    firstEq.symm.trans selected
  have endpoints : winner = pairing.winner ∧
      firstLoser = pairing.loser := by
    simpa using pairEq
  have loserEq : firstLoser = pairing.loser := endpoints.2
  simpa only [← loserEq] using firstInside

/-- Every loser selected by the second retained article batch belongs to the
same source payload. -/
theorem second_loser_mem_source
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {matching : List (Interface.Pairing n)}
    (agreement :
      ArticleBatchEndpointAgreement .second batches matching)
    {pairing : Interface.Pairing n}
    (member : pairing ∈ matching) :
    pairing.loser ∈ elements := by
  obtain ⟨row, rowMember, selected⟩ :=
    agreement.exists_row_of_mem member
  obtain ⟨winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, firstAdjacent, secondAdjacent,
      losersNe, candidatePerm, candidateChunk, candidateSegment,
      firstInBlock, secondInBlock, winnerInside, firstInside,
      secondInside⟩ :=
    certificate.retainedRow_inside batches rowMember
  simp only [articleRowSelection] at selected
  have pairEq : [winner, secondLoser] =
      [pairing.winner, pairing.loser] :=
    secondEq.symm.trans selected
  have endpoints : winner = pairing.winner ∧
      secondLoser = pairing.loser := by
    simpa using pairEq
  have loserEq : secondLoser = pairing.loser := endpoints.2
  simpa only [← loserEq] using secondInside

/-- Every winner selected by the first retained article batch belongs to the
same certified source payload. -/
theorem first_winner_mem_source
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement .first batches matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    pairing.winner ∈ elements := by
  obtain ⟨row, rowMember, selected⟩ := agreement.exists_row_of_mem member
  obtain ⟨winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, firstAdjacent, secondAdjacent,
      losersNe, candidatePerm, candidateChunk, candidateSegment,
      firstInBlock, secondInBlock, winnerInside, firstInside,
      secondInside⟩ := certificate.retainedRow_inside batches rowMember
  simp only [articleRowSelection] at selected
  have pairEq : [winner, firstLoser] =
      [pairing.winner, pairing.loser] := firstEq.symm.trans selected
  have endpoints : winner = pairing.winner ∧
      firstLoser = pairing.loser := by
    simpa using pairEq
  have winnerEq : winner = pairing.winner := endpoints.1
  simpa only [← winnerEq] using winnerInside

/-- Every winner selected by the second retained article batch also belongs
to the certified source payload. -/
theorem second_winner_mem_source
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement .second batches matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    pairing.winner ∈ elements := by
  obtain ⟨row, rowMember, selected⟩ := agreement.exists_row_of_mem member
  obtain ⟨winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, firstAdjacent, secondAdjacent,
      losersNe, candidatePerm, candidateChunk, candidateSegment,
      firstInBlock, secondInBlock, winnerInside, firstInside,
      secondInside⟩ := certificate.retainedRow_inside batches rowMember
  simp only [articleRowSelection] at selected
  have pairEq : [winner, secondLoser] =
      [pairing.winner, pairing.loser] := secondEq.symm.trans selected
  have endpoints : winner = pairing.winner ∧
      secondLoser = pairing.loser := by
    simpa using pairEq
  have winnerEq : winner = pairing.winner := endpoints.1
  simpa only [← winnerEq] using winnerInside

end ArticleInternalPairingFractionCertificate

/-- A block together with its stable identifier in one fixed rich state. -/
structure ArticleLocatedSource {n : ℕ} (state : Lazy.State n) where
  id : Interface.BlockId
  block : Lazy.Block n
  found : state.blocks[id]? = some block

namespace ArticleLocatedSource

/-- Distinct located block identifiers have disjoint payloads in every valid
rich state.  This exposes the global payload-separation fact in the exact
list form consumed by a request worklist. -/
theorem payloads_pairwise_disjoint
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (valid : state.Valid params)
    {sources : List (ArticleLocatedSource state)}
    (idsDistinct :
      sources.Pairwise fun first second => first.id ≠ second.id) :
    sources.Pairwise
      (Function.onFun List.Disjoint fun source =>
        source.block.elements) := by
  apply idsDistinct.imp
  intro first second idsNe
  simp only [Function.onFun, List.disjoint_left]
  intro element firstMember secondMember
  apply idsNe
  exact valid.blockId_eq_of_element_mem
    first.found firstMember second.found secondMember

end ArticleLocatedSource

/-- The source-local data needed for the global loser-uniqueness argument.

The record deliberately forgets destinations, values, and event positions.
It retains only the source payload, the two actual matchings, local
duplicate-freeness, and the fact that every loser came from that payload. -/
structure ArticleSourceLoserBatch (n : ℕ) where
  sourceElements : List (Interface.Element n)
  firstMatching : List (Interface.Pairing n)
  secondMatching : List (Interface.Pairing n)
  losersNodup :
    (Interface.pairingLosers (firstMatching ++ secondMatching)).Nodup
  loser_mem_source :
    ∀ loser ∈ Interface.pairingLosers
        (firstMatching ++ secondMatching),
      loser ∈ sourceElements
  winner_mem_source :
    ∀ pairing ∈ firstMatching ++ secondMatching,
      pairing.winner ∈ sourceElements

namespace ArticleSourceLoserBatch

/-- Package the exact global-uniqueness projection of one checked local
article certificate. -/
def ofSourcePairings
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ} {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches)
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement :
      ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement :
      ArticleBatchEndpointAgreement .second batches secondMatching) :
    ArticleSourceLoserBatch n where
  sourceElements := elements
  firstMatching := firstMatching
  secondMatching := secondMatching
  losersNodup :=
    plan.twoPhaseLosers_nodup firstAgreement secondAgreement
  loser_mem_source := by
    intro loser loserMember
    obtain ⟨pairing, pairingMember, pairingEq⟩ :=
      List.mem_map.mp (by
        simpa only [Interface.pairingLosers] using loserMember)
    subst loser
    rcases List.mem_append.mp pairingMember with firstMember | secondMember
    · exact (plan.endpoints_mem_source firstAgreement firstMember).2
    · exact (plan.endpoints_mem_source secondAgreement secondMember).2
  winner_mem_source := by
    intro pairing pairingMember
    rcases List.mem_append.mp pairingMember with firstMember | secondMember
    · exact (plan.endpoints_mem_source firstAgreement firstMember).1
    · exact (plan.endpoints_mem_source secondAgreement secondMember).1

def ofCertificate
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement :
      ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement :
      ArticleBatchEndpointAgreement .second batches secondMatching) :
    ArticleSourceLoserBatch n where
  sourceElements := elements
  firstMatching := firstMatching
  secondMatching := secondMatching
  losersNodup :=
    certificate.twoPhaseLosers_nodup batches firstAgreement secondAgreement
  loser_mem_source := by
    intro loser loserMember
    obtain ⟨pairing, pairingMember, pairingEq⟩ :=
      List.mem_map.mp (by
        simpa only [Interface.pairingLosers] using loserMember)
    subst loser
    rcases List.mem_append.mp pairingMember with firstMember | secondMember
    · exact certificate.first_loser_mem_source batches
        firstAgreement firstMember
    · exact certificate.second_loser_mem_source batches
        secondAgreement secondMember
  winner_mem_source := by
    intro pairing pairingMember
    rcases List.mem_append.mp pairingMember with firstMember | secondMember
    · exact certificate.first_winner_mem_source batches
        firstAgreement firstMember
    · exact certificate.second_winner_mem_source batches
        secondAgreement secondMember

/-- Pairwise-disjoint source payloads have pairwise-disjoint loser lists. -/
theorem loserLists_pairwise_disjoint
    {n : ℕ} {sources : List (ArticleSourceLoserBatch n)}
    (payloadsDisjoint :
      sources.Pairwise
        (Function.onFun List.Disjoint
          ArticleSourceLoserBatch.sourceElements)) :
    sources.Pairwise
      (Function.onFun List.Disjoint fun source =>
        Interface.pairingLosers
          (source.firstMatching ++ source.secondMatching)) := by
  apply payloadsDisjoint.imp
  intro first second payloadDisjoint
  simp only [Function.onFun, List.disjoint_left] at payloadDisjoint ⊢
  intro loser firstMember secondMember
  exact payloadDisjoint
    (first.loser_mem_source loser firstMember)
    (second.loser_mem_source loser secondMember)

/-- Global loser uniqueness for a complete request worklist.

This is the list-level lift missing from the one-source theorem: no loser can
occur twice within one source (the local result) or across distinct sources
(payload disjointness). -/
theorem globalLosers_nodup
    {n : ℕ} (sources : List (ArticleSourceLoserBatch n))
    (payloadsDisjoint :
      sources.Pairwise
        (Function.onFun List.Disjoint
          ArticleSourceLoserBatch.sourceElements)) :
    (sources.flatMap fun source =>
      Interface.pairingLosers
        (source.firstMatching ++ source.secondMatching)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨?_, loserLists_pairwise_disjoint payloadsDisjoint⟩
  intro source sourceMember
  exact source.losersNodup

end ArticleSourceLoserBatch

/-- A local loser batch tied to the concrete source block from which its
losers are removed. -/
structure ArticleLocatedLoserBatch
    {n : ℕ} (state : Lazy.State n) where
  source : ArticleLocatedSource state
  batch : ArticleSourceLoserBatch n
  sourceElements_eq : batch.sourceElements = source.block.elements

namespace ArticleLocatedLoserBatch

/-- Distinct concrete source identifiers imply global loser uniqueness
without an additional payload-disjointness hypothesis. -/
theorem globalLosers_nodup
    {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (valid : state.Valid params)
    (sources : List (ArticleLocatedLoserBatch state))
    (idsDistinct :
      sources.Pairwise fun first second =>
        first.source.id ≠ second.source.id) :
    (sources.flatMap fun source =>
      Interface.pairingLosers
        (source.batch.firstMatching ++
          source.batch.secondMatching)).Nodup := by
  have batchPayloads :
      (sources.map ArticleLocatedLoserBatch.batch).Pairwise
        (Function.onFun List.Disjoint
          ArticleSourceLoserBatch.sourceElements) := by
    rw [List.pairwise_map]
    apply idsDistinct.imp
    intro first second idsNe
    have concreteDisjoint :
        List.Disjoint first.source.block.elements
          second.source.block.elements := by
      simp only [List.disjoint_left]
      intro element firstMember secondMember
      exact idsNe
        (valid.blockId_eq_of_element_mem
          first.source.found firstMember
          second.source.found secondMember)
    simpa only [Function.onFun, first.sourceElements_eq,
      second.sourceElements_eq] using concreteDisjoint
  have global :=
    ArticleSourceLoserBatch.globalLosers_nodup
      (sources.map ArticleLocatedLoserBatch.batch) batchPayloads
  simpa only [List.flatMap_map, Function.comp_def] using global

end ArticleLocatedLoserBatch

end Splay.Accounting
