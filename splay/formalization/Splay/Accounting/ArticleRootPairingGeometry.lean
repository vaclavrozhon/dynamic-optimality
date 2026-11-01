import Splay.Accounting.ArticleSequentialPairingOrder
import Splay.Accounting.ArticleSourceExecution

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open ArticleBatchDestinationAllocation

/-- Source-free endpoint geometry in the complete frozen root child list. -/
theorem ArticleRetainedPairingBatches.rootGeometry
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups)
    (distinct : groups.Nodup) :
    ArticleSourcePairings
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0).reverse batches := by
  refine ⟨distinct, by simp, ?_⟩
  intro row member element inside
  obtain ⟨extra, winner, first, second, candidates, firstEq, secondEq,
    chunkEq, _, _, _, _, perm, _, _⟩ := batches.aligned row member
  have candidateMember : element ∈ candidates := by
    apply perm.mem_iff.mpr
    rw [firstEq, secondEq] at inside
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
    tauto
  have chunkMember : element ∈
      ((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0).drop
        (4 * row.1)).take 4 := by rw [chunkEq]; exact List.mem_cons_of_mem _ candidateMember
  simpa only [List.mem_reverse] using List.mem_of_mem_drop (List.mem_of_mem_take chunkMember)

/-- All phase endpoints are proper canonical children of the accessed root. -/
theorem ArticleBatchEndpointAgreement.root_parents
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    (distinct : groups.Nodup) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    canonicalParent snapshot before pairing.winner = some (valuePos ⟨key, key_lt_n⟩) ∧
      canonicalParent snapshot before pairing.loser = some (valuePos ⟨key, key_lt_n⟩) := by
  have inside := (batches.rootGeometry distinct).endpoints_mem_source agreement member
  have parent := (rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).parent
  have orderEq : (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0).reverse =
      (rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).elements := by
    simp [rootHeavyPathCanonicalChildOrder, rootHeavyPathChildrenBottomUp,
      rootHeavyPathChildrenTopDown, rootHeavyPathEdgesBottomUp, List.map_reverse]
  rw [orderEq] at inside
  exact ⟨parent _ inside.1, parent _ inside.2⟩

/-- Each actual phase pair is outermost in the canonical starting heap,
including a pair whose endpoints lie in different lazy source blocks. -/
theorem ArticleBatchEndpointAgreement.root_outermost
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase batches matching)
    (distinct : groups.Nodup) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    BatchOutermostOrder (canonicalHeapView snapshot before) matching := by
  intro pairing member child childMember
  have parents := agreement.root_parents distinct key_lt_n rankZero member
  have childFacts := (canonicalHeapView snapshot before).mem_topDown_iff.mp childMember
  have different : pairing.winner ≠ pairing.loser := by
    intro equal
    have strict := agreement.rank_lt member
    rw [equal] at strict
    exact Nat.lt_irrefl _ strict
  have result := (canonicalHeapView_nestedChildOrder snapshot before)
    parents.1 parents.2 different childFacts.1
    (by simpa [sideOf] using childFacts.2)
  by_cases left : pairing.loser.val < pairing.winner.val <;>
    simpa [sideOf, left] using result

/-- The geometric second-phase inequality survives the first phase without
assuming a common lazy source. Only the actual row alignment is used. -/
theorem ArticleBatchDestinationAllocation.BatchReparentedView.secondOutermost_of_ordered
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (order : batches.Ordered) {view : HeapView n}
    {firstMatching secondMatching : List (Interface.Pairing n)}
    (firstAgreement : ArticleBatchEndpointAgreement .first batches firstMatching)
    (secondAgreement : ArticleBatchEndpointAgreement .second batches secondMatching)
    (afterFirst : BatchReparentedView view firstMatching)
    (secondBaseOutermost : BatchOutermostOrder view secondMatching) :
    BatchOutermostOrder afterFirst.view secondMatching := by
  have firstWinnersNodup := pairingWinners_nodup (by
    rw [firstAgreement.matchingEndpoints_eq_rows]
    exact batches.firstEndpoints_nodup)
  have firstWinnerInjective :=
    List.inj_on_of_nodup_map firstWinnersNodup
  intro selected selectedMember child childMember
  have childFacts := afterFirst.view.mem_topDown_iff.mp childMember
  obtain ⟨row, rowMember, selectedRowEq⟩ :=
    secondAgreement.exists_row_of_mem selectedMember
  obtain ⟨winner, firstLoser, secondLoser, firstEq, secondEq, ordered⟩ := order row rowMember
  have selectedPairEq : [winner, secondLoser] =
      [selected.winner, selected.loser] := by
    exact secondEq.symm.trans selectedRowEq
  have selectedEndpoints : winner = selected.winner ∧
      secondLoser = selected.loser := by
    simpa using selectedPairEq
  by_cases moved : child ∈
      Interface.pairingLosers firstMatching
  · obtain ⟨movedPairing, movedMember, movedEq⟩ :=
      List.mem_map.mp (by
        simpa only [Interface.pairingLosers] using moved)
    obtain ⟨rowPairing, rowPairingMember, rowPairingEq⟩ :=
      forall₂_exists_right_of_mem_left firstAgreement rowMember
    have rowFirstPairEq : [winner, firstLoser] =
        [rowPairing.winner, rowPairing.loser] := by
      exact firstEq.symm.trans rowPairingEq
    have rowFirstEndpoints : winner = rowPairing.winner ∧
        firstLoser = rowPairing.loser := by
      simpa using rowFirstPairEq
    have movedParent := afterFirst.paired_parent movedPairing movedMember
    rw [movedEq] at movedParent
    have movedWinnerEq : movedPairing.winner = selected.winner :=
      Option.some.inj (movedParent.symm.trans childFacts.1)
    have rowWinnerEq : rowPairing.winner = selected.winner := by
      rw [← rowFirstEndpoints.1, selectedEndpoints.1]
    have pairingEq : movedPairing = rowPairing :=
      firstWinnerInjective movedMember rowPairingMember
        (movedWinnerEq.trans rowWinnerEq.symm)
    subst movedPairing
    have childEq : child = firstLoser := by
      exact movedEq.symm.trans rowFirstEndpoints.2.symm
    have childSideEq : afterFirst.view.side firstLoser =
        Splay.Lazy.Canonical.sideOf selected.winner selected.loser := by
      rw [← childEq]
      exact childFacts.2
    have sameSide :
        Splay.Lazy.Canonical.sideOf selected.winner firstLoser =
          Splay.Lazy.Canonical.sideOf selected.winner selected.loser := by
      have pairedSide :=
        afterFirst.paired_side rowPairing rowPairingMember
      have normalizedPairSide : afterFirst.view.side firstLoser =
          Splay.Lazy.Canonical.sideOf selected.winner firstLoser := by
        simpa only [← rowFirstEndpoints.2, rowWinnerEq] using pairedSide
      exact normalizedPairSide.symm.trans childSideEq
    have same : sideOf winner firstLoser = sideOf winner secondLoser := by
      simpa only [selectedEndpoints.1, selectedEndpoints.2] using sameSide
    have result := ordered same
    by_cases left : selected.loser.val < selected.winner.val <;>
      simpa [childEq, selectedEndpoints.1, selectedEndpoints.2, sideOf, left] using result
  · have notMoved : ∀ pairing ∈ firstMatching,
        child ≠ pairing.loser := by
      intro pairing pairingMember equal
      apply moved
      exact List.mem_map.mpr ⟨pairing, pairingMember, equal.symm⟩
    have originalChildParent :
        view.parent child = some selected.winner :=
      (afterFirst.unpaired_parent child notMoved).symm.trans childFacts.1
    have originalChildSide : view.side child =
        (if selected.loser.val < selected.winner.val then
          Side.left else Side.right) := by
      have sideEq :=
        (afterFirst.unpaired_side child notMoved).symm.trans childFacts.2
      simpa [Splay.Lazy.Canonical.sideOf] using sideEq
    have originalChildMember :
        child ∈ view.topDown selected.winner
          (Splay.Lazy.Canonical.sideOf selected.winner selected.loser) := by
      apply view.mem_topDown_iff.mpr
      exact ⟨originalChildParent, by
        simpa [Splay.Lazy.Canonical.sideOf] using originalChildSide⟩
    exact secondBaseOutermost selected selectedMember child originalChildMember


end Splay.Accounting
