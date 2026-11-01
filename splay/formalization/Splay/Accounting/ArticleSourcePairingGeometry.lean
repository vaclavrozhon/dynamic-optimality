import Splay.Accounting.ArticleAllPairingBatches
import Splay.Accounting.PairingSourceSublist

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical

/-- Source geometry needed for actual pairing, separated from the quantitative
fraction lemma. It applies also to a broken source's first exempt phases. -/
structure ArticleSourcePairings {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ} (elements : List (Interface.Element n))
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups) : Prop where
  groups_nodup : groups.Nodup
  sublist : elements.reverse.Sublist
    (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0)
  contained : ∀ row ∈ batches.rows, ∀ element ∈ row.2.1 ++ row.2.2, element ∈ elements

/-- Keep every literal triple contained in a source; all other triples remain
available for boundary classification. -/
noncomputable def ArticleSourcePairings.filtered {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ} (elements : List (Interface.Element n))
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups) :=
  batches.filter (fun row => decide (∀ element ∈ row.2.1 ++ row.2.2, element ∈ elements))

theorem ArticleSourcePairings.filtered_valid {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ} (elements : List (Interface.Element n))
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups)
    (distinct : groups.Nodup)
    (sourceSublist : elements.reverse.Sublist
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0)) :
    ArticleSourcePairings elements (filtered elements batches) := by
  refine ⟨batches.filtered_groups_nodup distinct _, sourceSublist, ?_⟩
  intro row member element inside
  have selected := (List.mem_filter.mp member).2
  exact (of_decide_eq_true selected) element inside

/-- Every retained row has its complete candidate triple inside this source. -/
theorem ArticleSourcePairings.row_inside
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (source : ArticleSourcePairings elements batches)
    {row : ℕ × (List (External n) × List (External n))}
    (rowMember : row ∈ batches.rows) :
    ∃ winner firstLoser secondLoser candidates,
      row.2.1 = [winner, firstLoser] ∧
        row.2.2 = [winner, secondLoser] ∧
        Interface.Adjacent candidates winner firstLoser ∧
        Interface.Adjacent (candidates.erase firstLoser)
          winner secondLoser ∧
        firstLoser ≠ secondLoser ∧
        candidates.Perm [winner, firstLoser, secondLoser] ∧
        IsSegment candidates
          ((rootHeavyPathChildrenBottomUp snapshot before
            (Nat.le_refl n) key 0 |>.drop (4 * row.1)).take 4) ∧
        IsSegment candidates elements.reverse ∧
        Interface.Adjacent elements winner firstLoser ∧
        Interface.Adjacent (elements.erase firstLoser)
          winner secondLoser ∧
        winner ∈ elements ∧ firstLoser ∈ elements ∧
        secondLoser ∈ elements := by
  obtain ⟨extra, winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, chunkEq, candidateLength, firstAdjacent,
      secondAdjacent, losersNe, candidatePerm, _firstRankLt,
      _secondRankLt⟩ :=
    batches.aligned row rowMember
  have candidateInChunk : IsSegment candidates
      ((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0
        |>.drop (4 * row.1)).take 4) := by
    exact ⟨[extra], [], by simpa using chunkEq⟩
  have candidateInAmbient : IsSegment candidates
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0) := by
    obtain ⟨front, back, chunkEq⟩ := candidateInChunk
    let whole := rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0
    refine ⟨whole.take (4 * row.1) ++ front, back ++ whole.drop (4 * row.1 + 4), ?_⟩
    have decomposition : whole = whole.take (4 * row.1) ++
        (whole.drop (4 * row.1)).take 4 ++ whole.drop (4 * row.1 + 4) := by
      rw [← List.drop_drop]
      rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
    calc
      whole = whole.take (4 * row.1) ++ (whole.drop (4 * row.1)).take 4 ++
          whole.drop (4 * row.1 + 4) := decomposition
      _ = _ := by rw [chunkEq]; simp [List.append_assoc]
  have candidateInBlockReverse : IsSegment candidates elements.reverse := by
    apply candidateInAmbient.in_sublist source.sublist
      (rootHeavyPathChildrenBottomUp_nodup snapshot before)
    intro element member
    have endpoint := candidatePerm.mem_iff.mp member
    have inside := source.contained _ rowMember element (by
      rw [firstEq, secondEq]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at endpoint ⊢
      tauto)
    simpa only [List.mem_reverse] using inside
  have elementsReverseNodup : elements.reverse.Nodup :=
    source.sublist.nodup (rootHeavyPathChildrenBottomUp_nodup snapshot before)
  have elementsNodup : elements.Nodup :=
    List.nodup_reverse.mp elementsReverseNodup
  have firstAdjacentInBlock :
      Interface.Adjacent elements winner firstLoser := by
    have inReverse := firstAdjacent.of_isSegment candidateInBlockReverse
    simpa using inReverse.reverse
  have firstLoserCandidate : firstLoser ∈ candidates :=
    candidatePerm.mem_iff.mpr (by simp)
  have firstLoserInside : firstLoser ∈ elements := by
    have reverseMember := candidateInBlockReverse.mem firstLoserCandidate
    simpa only [List.mem_reverse] using reverseMember
  have secondAdjacentInBlock :
      Interface.Adjacent (elements.erase firstLoser)
        winner secondLoser := by
    have erasedSegment := candidateInBlockReverse.erase elementsReverseNodup
      firstLoserCandidate
    have inReverse := secondAdjacent.of_isSegment erasedSegment
    rw [← List.reverse_erase_of_nodup elementsNodup firstLoserInside]
      at inReverse
    simpa using inReverse.reverse
  have endpointInside : ∀ endpoint ∈ [winner, firstLoser, secondLoser],
      endpoint ∈ elements := by
    intro endpoint endpointMember
    have candidateMember : endpoint ∈ candidates :=
      candidatePerm.mem_iff.mpr endpointMember
    have reverseMember := candidateInBlockReverse.mem candidateMember
    simpa only [List.mem_reverse] using reverseMember
  exact ⟨winner, firstLoser, secondLoser, candidates,
    firstEq, secondEq, firstAdjacent, secondAdjacent, losersNe,
    candidatePerm, candidateInChunk, candidateInBlockReverse,
    firstAdjacentInBlock,
    secondAdjacentInBlock, endpointInside winner (by simp),
    endpointInside firstLoser (by simp),
    endpointInside secondLoser (by simp)⟩


theorem ArticleSourcePairings.retainedFirstBatch_adjacent
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches) :
    ∀ row ∈ batches.rows,
      ∃ winner loser,
        row.2.1 = [winner, loser] ∧
          Interface.Adjacent elements winner loser := by
  intro row rowMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  exact ⟨winner, firstLoser, firstEq, firstInBlock⟩

/--
After all first-phase losers are removed simultaneously, every retained
second-phase pair is still adjacent.  This is the missing parallelism step
between the two `Pass` operations in the article: removals belonging to
other four-child groups cannot touch the current candidate triple.
-/
theorem ArticleSourcePairings.retainedSecondBatch_adjacent
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {groups : List ℕ}
    {elements : List (Interface.Element n)}
    {batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups}
    (plan : ArticleSourcePairings elements batches) :
    ∀ row ∈ batches.rows,
      ∃ winner loser,
        row.2.2 = [winner, loser] ∧
          Interface.Adjacent
            (batches.firstLosers.foldl List.erase elements)
            winner loser := by
  have elementsReverseNodup : elements.reverse.Nodup :=
    plan.sublist.nodup (rootHeavyPathChildrenBottomUp_nodup snapshot before)
  have elementsNodup : elements.Nodup :=
    List.nodup_reverse.mp elementsReverseNodup
  have groupMapNodup : (batches.rows.map Prod.fst).Nodup :=
    batches.groups_perm.nodup_iff.mpr plan.groups_nodup
  intro row rowMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    plan.row_inside rowMember
  have winnerNeFirstLoser : winner ≠ firstLoser :=
    firstInBlock.ne_of_nodup elementsNodup
  have firstLoserRemoval : firstLoser ∈ batches.firstLosers := by
    apply List.mem_filterMap.mpr
    refine ⟨row, rowMember, ?_⟩
    rw [firstEq]
    simp
  have removalFresh : ∀ removed ∈ batches.firstLosers,
      removed ≠ winner ∧ removed ≠ secondLoser := by
    intro removed removedMember
    obtain ⟨otherRow, otherRowMember, otherFound⟩ :=
      List.mem_filterMap.mp removedMember
    obtain ⟨otherWinner, otherFirstLoser, otherSecondLoser,
        otherCandidates, otherFirstEq, otherSecondEq, otherFirstAdjacent,
        otherSecondAdjacent, otherLosersNe, otherCandidatePerm,
        otherCandidateChunk, otherCandidateSegment, otherFirstInBlock,
        otherSecondInBlock, otherWinnerInside, otherFirstInside,
        otherSecondInside⟩ :=
      plan.row_inside otherRowMember
    rw [otherFirstEq] at otherFound
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at otherFound
    subst removed
    by_cases sameGroup : otherRow.1 = row.1
    · have rowsEq : otherRow = row :=
        List.inj_on_of_nodup_map groupMapNodup
          otherRowMember rowMember sameGroup
      subst otherRow
      have pairEq : [otherWinner, otherFirstLoser] =
          [winner, firstLoser] := otherFirstEq.symm.trans firstEq
      have endpointEq : otherWinner = winner ∧
          otherFirstLoser = firstLoser := by simpa using pairEq
      rw [endpointEq.2]
      exact ⟨winnerNeFirstLoser.symm, losersNe⟩
    · have otherFirstCandidate : otherFirstLoser ∈ otherCandidates :=
        otherCandidatePerm.mem_iff.mpr (by simp)
      have otherFirstChunk :=
        otherCandidateChunk.mem otherFirstCandidate
      have winnerCandidate : winner ∈ candidates :=
        candidatePerm.mem_iff.mpr (by simp)
      have winnerChunk := candidateChunk.mem winnerCandidate
      have secondCandidate : secondLoser ∈ candidates :=
        candidatePerm.mem_iff.mpr (by simp)
      have secondChunk := candidateChunk.mem secondCandidate
      constructor
      · intro equal
        subst otherFirstLoser
        exact groupChunks_disjoint_of_nodup
          (rootHeavyPathChildrenBottomUp_nodup snapshot before)
          sameGroup otherFirstChunk winnerChunk
      · intro equal
        subst otherFirstLoser
        exact groupChunks_disjoint_of_nodup
          (rootHeavyPathChildrenBottomUp_nodup snapshot before)
          sameGroup otherFirstChunk secondChunk
  exact ⟨winner, secondLoser, secondEq,
    secondInBlock.foldl_erase_of_mem firstLoserRemoval removalFresh⟩


/-- Existing unbroken fraction certificates provide the more general source
geometry used by both ordinary and exempt pass implementations. -/
theorem ArticleInternalPairingFractionCertificate.sourcePairings
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {elements : List (Interface.Element n)}
    (certificate : ArticleInternalPairingFractionCertificate kinds elements
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key certificate.fraction.groups) :
    ArticleSourcePairings elements batches := by
  refine ⟨certificate.fraction.groups_nodup, ?_, ?_⟩
  · exact IsSegment.sublist ⟨certificate.front, certificate.back, certificate.decomposition⟩
  · intro row member element endpoint
    obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq, secondEq,
      _, _, _, _, _, _, _, _, winnerInside, firstInside, secondInside⟩ :=
      certificate.retainedRow_inside batches member
    rw [firstEq, secondEq] at endpoint
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at endpoint
    rcases endpoint with (rfl | rfl) | (rfl | rfl)
    · exact winnerInside
    · exact firstInside
    · exact winnerInside
    · exact secondInside

end Splay.Accounting
