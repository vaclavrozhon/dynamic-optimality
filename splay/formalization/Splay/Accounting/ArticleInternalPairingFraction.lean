import Splay.Accounting.RootHeavyPathFullOrder
import Splay.Accounting.InternalPairingFractionGeometry
import Splay.Accounting.InternalPhasePairingAlignment
import Splay.Accounting.ArticlePairingSchedule

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical

/--
The article's complete internal zig-zig groups, retaining their actual four
ambient child positions rather than only the numerical fraction bound.
-/
structure ArticleInternalPairingFractionCertificate
    {n : ℕ} (kinds : List SplayStepKind)
    (elements bottomUp : List (Interface.Element n)) where
  fraction :
    InternalPairingFractionWitness kinds elements.reverse.length
  front : List (Interface.Element n)
  back : List (Interface.Element n)
  decomposition : bottomUp = front ++ elements.reverse ++ back
  groups_eq :
    fraction.groups =
      completeDoubleGroups front.length elements.reverse.length

/--
The two concrete article batches after discarding zig-zig groups that cross
the boundary of the current lazy interval.  A row keeps the global group
index together with its first- and second-phase endpoint pair.

The two endpoint batches are the `flatMap`s in the last two fields.  Their
duplicate-freeness is exactly the simultaneous-matching condition that is
independent of destinations and values.
-/
structure ArticleRetainedPairingBatches
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (before : BST lower upper) (upper_le_n : upper ≤ n)
    (key : ℕ) (eligibleGroups : List ℕ) where
  rows : List (ℕ × (List (External n) × List (External n)))
  groups_perm : (rows.map Prod.fst).Perm eligibleGroups
  aligned :
    ∀ row ∈ rows,
      SequentialPhaseSelectionAtDoubleGroup
        snapshot before upper_le_n key row.1 row.2
  firstEndpoints_nodup :
    (rows.flatMap fun row => row.2.1).Nodup
  secondEndpoints_nodup :
    (rows.flatMap fun row => row.2.2).Nodup

namespace ArticleRetainedPairingBatches

/-- The elements removed from the shrinking source by the first article
phase, in retained-row order. -/
def firstLosers
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    (batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups) :
    List (External n) :=
  batches.rows.filterMap fun row => row.2.1[1]?

/-- Each retained group contributes exactly one row to both batches. -/
theorem length_eq_eligibleGroups_length
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n}
    {eligibleGroups : List ℕ}
    (batches : ArticleRetainedPairingBatches
      snapshot before upper_le_n key eligibleGroups) :
    batches.rows.length = eligibleGroups.length := by
  simpa using batches.groups_perm.length_eq

end ArticleRetainedPairingBatches

/-- All four child positions of every certified group belong to the block. -/
theorem ArticleInternalPairingFractionCertificate.group_inside
    {n : ℕ} {kinds : List SplayStepKind}
    {elements bottomUp : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements bottomUp)
    {group : ℕ} (groupMember : group ∈ certificate.fraction.groups)
    {offset : ℕ} (offsetLt : offset < 4) :
    ∃ element,
      bottomUp[4 * group + offset]? = some element ∧
        element ∈ elements := by
  rw [certificate.groups_eq] at groupMember
  obtain ⟨element, found, reverseMember⟩ :=
    getElem?_mem_of_completeDoubleGroup certificate.decomposition
      groupMember offsetLt
  exact ⟨element, found, by
    simpa only [List.mem_reverse] using reverseMember⟩

/-- Every member of the concrete four-child chunk belongs to the block. -/
theorem ArticleInternalPairingFractionCertificate.mem_of_mem_groupChunk
    {n : ℕ} {kinds : List SplayStepKind}
    {elements bottomUp : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements bottomUp)
    {group : ℕ} (groupMember : group ∈ certificate.fraction.groups)
    {element : Interface.Element n}
    (member : element ∈ (bottomUp.drop (4 * group)).take 4) :
    element ∈ elements := by
  obtain ⟨offset, found⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_take] at found
  split at found
  next offsetLt =>
    rw [List.getElem?_drop] at found
    obtain ⟨selected, selectedFound, selectedMember⟩ :=
      certificate.group_inside groupMember offsetLt
    have selectedEq : selected = element := by
      apply Option.some.inj
      rw [← selectedFound]
      simpa only [Nat.add_comm] using found
    simpa only [selectedEq] using selectedMember
  next offsetGe =>
    simp at found

/-- Normalize a certified ambient group to a slice of the block itself. -/
theorem ArticleInternalPairingFractionCertificate.groupChunk_eq_blockSlice
    {n : ℕ} {kinds : List SplayStepKind}
    {elements bottomUp : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements bottomUp)
    {group : ℕ} (groupMember : group ∈ certificate.fraction.groups) :
    (bottomUp.drop (4 * group)).take 4 =
      (elements.reverse.drop
        (4 * group - certificate.front.length)).take 4 := by
  rw [certificate.groups_eq] at groupMember
  have startLe :=
    start_le_four_mul_of_mem_completeDoubleGroups groupMember
  have endLe :=
    four_mul_add_four_le_end_of_mem_completeDoubleGroups groupMember
  conv_lhs => rw [certificate.decomposition, List.append_assoc]
  rw [List.drop_append]
  have frontDrop : certificate.front.drop (4 * group) = [] :=
    List.drop_eq_nil_iff.mpr startLe
  rw [frontDrop, List.nil_append]
  rw [List.drop_append]
  have insideTake :
      ((elements.reverse.drop
          (4 * group - certificate.front.length)) ++
        certificate.back.drop
          (4 * group - certificate.front.length -
            elements.reverse.length)).take 4 =
      (elements.reverse.drop
        (4 * group - certificate.front.length)).take 4 := by
    rw [List.take_append_of_le_length]
    simp only [List.length_drop]
    omega
  exact insideTake

/-- Every certified four-child group is itself consecutive in the block. -/
theorem ArticleInternalPairingFractionCertificate.groupChunk_isSegment
    {n : ℕ} {kinds : List SplayStepKind}
    {elements bottomUp : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements bottomUp)
    {group : ℕ} (groupMember : group ∈ certificate.fraction.groups) :
    IsSegment ((bottomUp.drop (4 * group)).take 4) elements.reverse := by
  rw [certificate.groupChunk_eq_blockSlice groupMember]
  apply IsSegment.take
  apply IsSegment.drop
  exact ⟨[], [], by simp⟩

private theorem exists_index_of_mem_groupChunk
    {α : Type*} {bottomUp : List α} {group : ℕ} {element : α}
    (member : element ∈ (bottomUp.drop (4 * group)).take 4) :
    ∃ offset, offset < 4 ∧
      bottomUp[4 * group + offset]? = some element := by
  obtain ⟨offset, found⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_take] at found
  split at found
  next offsetLt =>
    rw [List.getElem?_drop] at found
    exact ⟨offset, offsetLt, by simpa only [Nat.add_comm] using found⟩
  next offsetGe => simp at found

/-- Distinct four-child groups in a duplicate-free ambient order are
element-disjoint. -/
theorem groupChunks_disjoint_of_nodup
    {α : Type*} {bottomUp : List α} (nodup : bottomUp.Nodup)
    {firstGroup secondGroup : ℕ} (groupsNe : firstGroup ≠ secondGroup)
    {element : α}
    (firstMember :
      element ∈ (bottomUp.drop (4 * firstGroup)).take 4)
    (secondMember :
      element ∈ (bottomUp.drop (4 * secondGroup)).take 4) : False := by
  obtain ⟨firstOffset, firstOffsetLt, firstFound⟩ :=
    exists_index_of_mem_groupChunk firstMember
  obtain ⟨secondOffset, secondOffsetLt, secondFound⟩ :=
    exists_index_of_mem_groupChunk secondMember
  obtain ⟨firstBound, firstGet⟩ :=
    List.getElem?_eq_some_iff.mp firstFound
  obtain ⟨secondBound, secondGet⟩ :=
    List.getElem?_eq_some_iff.mp secondFound
  have indexEq : 4 * firstGroup + firstOffset =
      4 * secondGroup + secondOffset :=
    nodup.getElem_inj_iff.mp (firstGet.trans secondGet.symm)
  apply groupsNe
  omega

/--
Every actual phase pair selected for a certified internal group stays inside
the lazy block.  This closes the incidence bridge between the numerical
four-child grouping and `PhaseSelections` from the concrete splay.
-/
theorem ArticleInternalPairingFractionCertificate.exists_phaseSelection_inside
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    {selections : List (List (External n))}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (aligned :
      List.Forall₂
        (PhaseSelectionSupportedAtDoubleGroup
          snapshot before (Nat.le_refl n) execution)
        (zigZigDoubleGroupIndices kinds 0) selections)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {group : ℕ} (groupMember : group ∈ certificate.fraction.groups) :
    ∃ children,
      children ∈ selections ∧
        PhaseSelectionSupportedAtDoubleGroup
          snapshot before (Nat.le_refl n) execution group children ∧
        children.length = 2 ∧ children.Nodup ∧
        ∀ child ∈ children, child ∈ elements := by
  have flag := certificate.fraction.internal_zigZig group groupMember
  have groupAligned : group ∈ zigZigDoubleGroupIndices kinds 0 :=
    mem_zigZigDoubleGroupIndices_zero_of_doubleStepFlags_eq_true flag
  obtain ⟨children, selectionMember, supported⟩ :=
    forall₂_exists_right_of_mem_left aligned groupAligned
  refine ⟨children, selectionMember, supported, supported.1,
    supported.2.1, ?_⟩
  intro child childMember
  apply certificate.mem_of_mem_groupChunk groupMember
  exact supported.mem_rootHeavyPathChildrenGroup
    key_lt_n rankZero childMember

/--
For either manuscript phase, choose all genuine zig-zig pairs in parallel.
Their global endpoint batch is duplicate-free, and every group certified as
internal has its corresponding two endpoints wholly inside the block.
-/
theorem ArticleInternalPairingFractionCertificate.exists_phaseSelections_inside
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {blockElements : List (Interface.Element n)}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (certificate :
      ArticleInternalPairingFractionCertificate kinds blockElements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (phase : PairingPhase) :
    ∃ selections : List (List (External n)),
      SplayExecutionTranscript.PhaseSelections
          snapshot phase key transcript selections ∧
        selections.flatten.Nodup ∧
        ∀ group ∈ certificate.fraction.groups,
          ∃ children,
            children ∈ selections ∧
              children.length = 2 ∧ children.Nodup ∧
              ∀ child ∈ children, child ∈ blockElements := by
  obtain ⟨selections, actual, aligned, nodup⟩ :=
    transcript.exists_phaseSelections_atDoubleGroups
      (Nat.le_refl n) key_lt_n rankZero phase
  refine ⟨selections, actual, nodup, ?_⟩
  intro group groupMember
  obtain ⟨children, selectionMember, _, lengthTwo, childrenNodup,
      inside⟩ :=
    certificate.exists_phaseSelection_inside aligned key_lt_n rankZero
      groupMember
  exact ⟨children, selectionMember, lengthTwo, childrenNodup, inside⟩

/-- Both article phases, with actual duplicate-free endpoints inside the block. -/
theorem ArticleInternalPairingFractionCertificate.exists_bothPhaseSelections_inside
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {blockElements : List (Interface.Element n)}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (certificate :
      ArticleInternalPairingFractionCertificate kinds blockElements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections : List (List (External n)),
      SplayExecutionTranscript.PhaseSelections
          snapshot .first key transcript firstSelections ∧
        SplayExecutionTranscript.PhaseSelections
          snapshot .second key transcript secondSelections ∧
        firstSelections.flatten.Nodup ∧
        secondSelections.flatten.Nodup ∧
        (∀ group ∈ certificate.fraction.groups,
          ∃ children,
            children ∈ firstSelections ∧
              children.length = 2 ∧ children.Nodup ∧
              ∀ child ∈ children, child ∈ blockElements) ∧
        (∀ group ∈ certificate.fraction.groups,
          ∃ children,
            children ∈ secondSelections ∧
              children.length = 2 ∧ children.Nodup ∧
              ∀ child ∈ children, child ∈ blockElements) := by
  obtain ⟨firstSelections, firstActual, firstNodup, firstInside⟩ :=
    certificate.exists_phaseSelections_inside transcript key_lt_n rankZero
      .first
  obtain ⟨secondSelections, secondActual, secondNodup, secondInside⟩ :=
    certificate.exists_phaseSelections_inside transcript key_lt_n rankZero
      .second
  exact ⟨firstSelections, secondSelections, firstActual, secondActual,
    firstNodup, secondNodup, firstInside, secondInside⟩

/--
Stronger two-phase form retaining that the first and second pair for each
zig-zig come from one sequential local configuration.
-/
theorem ArticleInternalPairingFractionCertificate.exists_jointPhaseSelections_inside
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {blockElements : List (Interface.Element n)}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (certificate :
      ArticleInternalPairingFractionCertificate kinds blockElements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections : List (List (External n)),
      SplayExecutionTranscript.BothPhaseSelections
          snapshot key transcript firstSelections secondSelections ∧
        firstSelections.flatten.Nodup ∧
        secondSelections.flatten.Nodup ∧
        (∀ group ∈ certificate.fraction.groups,
          ∃ children,
            children ∈ firstSelections ∧
              children.length = 2 ∧ children.Nodup ∧
              ∀ child ∈ children, child ∈ blockElements) ∧
        (∀ group ∈ certificate.fraction.groups,
          ∃ children,
            children ∈ secondSelections ∧
              children.length = 2 ∧ children.Nodup ∧
              ∀ child ∈ children, child ∈ blockElements) := by
  obtain ⟨firstSelections, secondSelections, joint, firstAligned,
      secondAligned, firstNodup, secondNodup⟩ :=
    transcript.exists_bothPhaseSelections_atDoubleGroups
      (Nat.le_refl n) key_lt_n rankZero
  refine ⟨firstSelections, secondSelections, joint, firstNodup, secondNodup,
    ?_, ?_⟩
  · intro group groupMember
    obtain ⟨children, selectionMember, _, lengthTwo, childrenNodup,
        inside⟩ :=
      certificate.exists_phaseSelection_inside firstAligned key_lt_n
        rankZero groupMember
    exact ⟨children, selectionMember, lengthTwo, childrenNodup, inside⟩
  · intro group groupMember
    obtain ⟨children, selectionMember, _, lengthTwo, childrenNodup,
        inside⟩ :=
      certificate.exists_phaseSelection_inside secondAligned key_lt_n
        rankZero groupMember
    exact ⟨children, selectionMember, lengthTwo, childrenNodup, inside⟩

/--
A certified internal group has its same-winner first/second pair inside the
block, with the exact sequential adjacency and contiguous candidate run from
the manuscript.
-/
theorem ArticleInternalPairingFractionCertificate.exists_jointSelection_inside
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {elements : List (Interface.Element n)}
    {firstSelections secondSelections : List (List (External n))}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (joint : SplayExecutionTranscript.BothPhaseSelections
      snapshot key transcript firstSelections secondSelections)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {group : ℕ} (groupMember : group ∈ certificate.fraction.groups) :
    ∃ firstSelection secondSelection winner firstLoser secondLoser candidates,
      firstSelection ∈ firstSelections ∧
        secondSelection ∈ secondSelections ∧
        firstSelection = [winner, firstLoser] ∧
        secondSelection = [winner, secondLoser] ∧
        Interface.Adjacent candidates winner firstLoser ∧
        Interface.Adjacent (candidates.erase firstLoser)
          winner secondLoser ∧
        firstLoser ≠ secondLoser ∧
        candidates.Perm [winner, firstLoser, secondLoser] ∧
        IsSegment candidates elements.reverse ∧
        Interface.Adjacent elements winner firstLoser ∧
        Interface.Adjacent (elements.erase firstLoser) winner secondLoser ∧
        winner ∈ elements ∧ firstLoser ∈ elements ∧
        secondLoser ∈ elements := by
  have flag := certificate.fraction.internal_zigZig group groupMember
  have groupAligned : group ∈ zigZigDoubleGroupIndices kinds 0 :=
    mem_zigZigDoubleGroupIndices_zero_of_doubleStepFlags_eq_true flag
  obtain ⟨firstSelection, secondSelection, extra, winner, firstLoser,
      secondLoser, candidates, firstMember, secondMember, firstEq, secondEq,
      chunkEq, candidateLength, firstAdjacent, secondAdjacent, losersNe,
      candidatePerm⟩ :=
    joint.exists_sequential_atDoubleGroup
      (Nat.le_refl n) key_lt_n rankZero groupAligned
  have candidateInChunk : IsSegment candidates
      ((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0
        |>.drop (4 * group)).take 4) := by
    exact ⟨[extra], [], by simpa using chunkEq⟩
  have chunkInBlock := certificate.groupChunk_isSegment groupMember
  have candidateInBlockReverse : IsSegment candidates elements.reverse := by
    obtain ⟨candidateFront, candidateBack, candidateDecomposition⟩ :=
      candidateInChunk
    obtain ⟨chunkFront, chunkBack, chunkDecomposition⟩ := chunkInBlock
    refine ⟨chunkFront ++ candidateFront, candidateBack ++ chunkBack, ?_⟩
    rw [chunkDecomposition, candidateDecomposition]
    simp [List.append_assoc]
  have blockReverseSegment : IsSegment elements.reverse
      (rootHeavyPathChildrenBottomUp
        snapshot before (Nat.le_refl n) key 0) :=
    ⟨certificate.front, certificate.back, certificate.decomposition⟩
  have elementsReverseNodup : elements.reverse.Nodup :=
    (Splay.Lazy.Canonical.IsSegment.sublist blockReverseSegment).nodup
      (rootHeavyPathChildrenBottomUp_nodup snapshot before)
  have elementsNodup : elements.Nodup :=
    List.nodup_reverse.mp elementsReverseNodup
  have firstAdjacentInBlock :
      Interface.Adjacent elements winner firstLoser := by
    have inReverse := firstAdjacent.of_isSegment candidateInBlockReverse
    simpa using inReverse.reverse
  have firstLoserCandidate : firstLoser ∈ candidates :=
    candidatePerm.mem_iff.mpr (by simp)
  have firstLoserInside : firstLoser ∈ elements := by
    have reverseMember :=
      candidateInBlockReverse.mem firstLoserCandidate
    simpa only [List.mem_reverse] using reverseMember
  have secondAdjacentInBlock :
      Interface.Adjacent (elements.erase firstLoser) winner secondLoser := by
    have erasedSegment := candidateInBlockReverse.erase elementsReverseNodup
      firstLoserCandidate
    have inReverse := secondAdjacent.of_isSegment erasedSegment
    rw [← List.reverse_erase_of_nodup elementsNodup firstLoserInside] at inReverse
    simpa using inReverse.reverse
  have endpointInside : ∀ endpoint ∈ [winner, firstLoser, secondLoser],
      endpoint ∈ elements := by
    intro endpoint endpointMember
    have candidateMember : endpoint ∈ candidates :=
      candidatePerm.mem_iff.mpr endpointMember
    have reverseMember := candidateInBlockReverse.mem candidateMember
    simpa only [List.mem_reverse] using reverseMember
  refine ⟨firstSelection, secondSelection, winner, firstLoser, secondLoser,
    candidates, firstMember, secondMember, firstEq, secondEq,
    firstAdjacent, secondAdjacent, losersNe, candidatePerm,
    candidateInBlockReverse, firstAdjacentInBlock, secondAdjacentInBlock,
    endpointInside winner (by simp),
    endpointInside firstLoser (by simp), endpointInside secondLoser (by simp)⟩

/--
Filter the joint transcript by the complete groups contained in the block.
The result is the article's two parallel endpoint batches: there is exactly
one row per certified internal group, both rows stay positionally aligned,
and the endpoints used within either phase are duplicate-free.
-/
theorem ArticleInternalPairingFractionCertificate.exists_retainedPairingBatches
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {elements : List (Interface.Element n)}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    Nonempty (ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups) := by
  obtain ⟨firstSelections, secondSelections, joint, firstAligned,
      secondAligned, firstNodup, secondNodup⟩ :=
    transcript.exists_bothPhaseSelections_atDoubleGroups
      (Nat.le_refl n) key_lt_n rankZero
  let allGroups := zigZigDoubleGroupIndices kinds 0
  let selectionPairs := firstSelections.zip secondSelections
  let allRows := allGroups.zip selectionPairs
  let retainGroup : ℕ → Bool := fun group =>
    decide (group ∈ certificate.fraction.groups)
  let rows := allRows.filter (retainGroup ∘ Prod.fst)
  have positionAligned : List.Forall₂
      (SequentialPhaseSelectionAtDoubleGroup
        snapshot before (Nat.le_refl n) key)
      allGroups selectionPairs := by
    exact joint.forall₂_sequential_atDoubleGroups
      (Nat.le_refl n) key_lt_n rankZero
  have phaseLength : firstSelections.length = secondSelections.length :=
    joint.forall₂_sequential.length_eq
  have allGroupProjection : allRows.map Prod.fst = allGroups := by
    exact List.map_fst_zip (le_of_eq positionAligned.length_eq)
  have retainedGroupProjection :
      rows.map Prod.fst =
        allGroups.filter fun group =>
          decide (group ∈ certificate.fraction.groups) := by
    dsimp only [rows]
    rw [← List.filter_map]
    rw [allGroupProjection]
  have eligibleSubset : certificate.fraction.groups ⊆ allGroups := by
    intro group groupMember
    exact mem_zigZigDoubleGroupIndices_zero_of_doubleStepFlags_eq_true
      (certificate.fraction.internal_zigZig group groupMember)
  have retainedGroupsNodup : (rows.map Prod.fst).Nodup := by
    rw [retainedGroupProjection]
    exact (zigZigDoubleGroupIndices_nodup kinds 0).filter _
  have retainedGroupsPerm :
      (rows.map Prod.fst).Perm certificate.fraction.groups := by
    apply (List.perm_ext_iff_of_nodup retainedGroupsNodup
      certificate.fraction.groups_nodup).mpr
    intro group
    rw [retainedGroupProjection]
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun member => member.2
    · intro member
      exact ⟨eligibleSubset member, member⟩
  have rowAligned : ∀ row ∈ rows,
      SequentialPhaseSelectionAtDoubleGroup
        snapshot before (Nat.le_refl n) key row.1 row.2 := by
    intro row rowMember
    have allRowMember : row ∈ allRows :=
      (List.mem_filter.mp rowMember).1
    exact List.forall₂_zip positionAligned allRowMember
  have firstProjection :
      allRows.map (fun row => row.2.1) = firstSelections := by
    calc
      allRows.map (fun row => row.2.1) =
          (allRows.map Prod.snd).map Prod.fst := by
            simp only [List.map_map, Function.comp_def]
      _ = selectionPairs.map Prod.fst := by
            rw [List.map_snd_zip
              (le_of_eq positionAligned.length_eq.symm)]
      _ = firstSelections := by
            exact List.map_fst_zip (le_of_eq phaseLength)
  have secondProjection :
      allRows.map (fun row => row.2.2) = secondSelections := by
    calc
      allRows.map (fun row => row.2.2) =
          (allRows.map Prod.snd).map Prod.snd := by
            simp only [List.map_map, Function.comp_def]
      _ = selectionPairs.map Prod.snd := by
            rw [List.map_snd_zip
              (le_of_eq positionAligned.length_eq.symm)]
      _ = secondSelections := by
            exact List.map_snd_zip (le_of_eq phaseLength.symm)
  have filteredSublist : List.Sublist rows allRows := List.filter_sublist
  have firstListsSublist :
      List.Sublist (rows.map (fun row => row.2.1)) firstSelections := by
    have mapped := filteredSublist.map (fun row => row.2.1)
    rw [firstProjection] at mapped
    exact mapped
  have secondListsSublist :
      List.Sublist (rows.map (fun row => row.2.2)) secondSelections := by
    have mapped := filteredSublist.map (fun row => row.2.2)
    rw [secondProjection] at mapped
    exact mapped
  have retainedFirstNodup :
      (rows.flatMap fun row => row.2.1).Nodup := by
    rw [List.flatMap_def]
    exact List.Nodup.sublist firstListsSublist.flatten firstNodup
  have retainedSecondNodup :
      (rows.flatMap fun row => row.2.2).Nodup := by
    rw [List.flatMap_def]
    exact List.Nodup.sublist secondListsSublist.flatten secondNodup
  exact ⟨{
    rows := rows
    groups_perm := retainedGroupsPerm
    aligned := rowAligned
    firstEndpoints_nodup := retainedFirstNodup
    secondEndpoints_nodup := retainedSecondNodup
  }⟩

/--
Every retained row is an actual pair in the block in both manuscript phases.
The second adjacency is stated after removing that row's first loser, which
is the local state change between the two zig-zig pair-ups.
-/
theorem ArticleInternalPairingFractionCertificate.retainedRow_inside
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups)
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
  have groupInRows : row.1 ∈ batches.rows.map Prod.fst :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  have groupMember : row.1 ∈ certificate.fraction.groups :=
    batches.groups_perm.mem_iff.mp groupInRows
  obtain ⟨extra, winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, chunkEq, candidateLength, firstAdjacent,
      secondAdjacent, losersNe, candidatePerm, _firstRankLt,
      _secondRankLt⟩ :=
    batches.aligned row rowMember
  have candidateInChunk : IsSegment candidates
      ((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0
        |>.drop (4 * row.1)).take 4) := by
    exact ⟨[extra], [], by simpa using chunkEq⟩
  have chunkInBlock := certificate.groupChunk_isSegment groupMember
  have candidateInBlockReverse : IsSegment candidates elements.reverse := by
    obtain ⟨candidateFront, candidateBack, candidateDecomposition⟩ :=
      candidateInChunk
    obtain ⟨chunkFront, chunkBack, chunkDecomposition⟩ := chunkInBlock
    refine ⟨chunkFront ++ candidateFront, candidateBack ++ chunkBack, ?_⟩
    rw [chunkDecomposition, candidateDecomposition]
    simp [List.append_assoc]
  have blockReverseSegment : IsSegment elements.reverse
      (rootHeavyPathChildrenBottomUp
        snapshot before (Nat.le_refl n) key 0) :=
    ⟨certificate.front, certificate.back, certificate.decomposition⟩
  have elementsReverseNodup : elements.reverse.Nodup :=
    (Splay.Lazy.Canonical.IsSegment.sublist blockReverseSegment).nodup
      (rootHeavyPathChildrenBottomUp_nodup snapshot before)
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

/-- The first retained endpoint batch is already a simultaneous geometric
matching in the source block (destinations are deliberately added later). -/
theorem ArticleInternalPairingFractionCertificate.retainedFirstBatch_adjacent
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups) :
    ∀ row ∈ batches.rows,
      ∃ winner loser,
        row.2.1 = [winner, loser] ∧
          Interface.Adjacent elements winner loser := by
  intro row rowMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    certificate.retainedRow_inside batches rowMember
  exact ⟨winner, firstLoser, firstEq, firstInBlock⟩

/--
After all first-phase losers are removed simultaneously, every retained
second-phase pair is still adjacent.  This is the missing parallelism step
between the two `Pass` operations in the article: removals belonging to
other four-child groups cannot touch the current candidate triple.
-/
theorem ArticleInternalPairingFractionCertificate.retainedSecondBatch_adjacent
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind}
    {elements : List (Interface.Element n)}
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key certificate.fraction.groups) :
    ∀ row ∈ batches.rows,
      ∃ winner loser,
        row.2.2 = [winner, loser] ∧
          Interface.Adjacent
            (batches.firstLosers.foldl List.erase elements)
            winner loser := by
  have blockReverseSegment : IsSegment elements.reverse
      (rootHeavyPathChildrenBottomUp
        snapshot before (Nat.le_refl n) key 0) :=
    ⟨certificate.front, certificate.back, certificate.decomposition⟩
  have elementsReverseNodup : elements.reverse.Nodup :=
    (Splay.Lazy.Canonical.IsSegment.sublist blockReverseSegment).nodup
      (rootHeavyPathChildrenBottomUp_nodup snapshot before)
  have elementsNodup : elements.Nodup :=
    List.nodup_reverse.mp elementsReverseNodup
  have groupMapNodup : (batches.rows.map Prod.fst).Nodup :=
    batches.groups_perm.nodup_iff.mpr certificate.fraction.groups_nodup
  intro row rowMember
  obtain ⟨winner, firstLoser, secondLoser, candidates, firstEq,
      secondEq, firstAdjacent, secondAdjacent, losersNe, candidatePerm,
      candidateChunk, candidateSegment, firstInBlock, secondInBlock,
      winnerInside, firstInside, secondInside⟩ :=
    certificate.retainedRow_inside batches rowMember
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
      certificate.retainedRow_inside batches otherRowMember
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

/--
Combined article-level scheduler certificate before block operations are
executed: every counted group has one genuine sequential pair, both phase
batches are duplicate-free, and all three endpoints lie in the source block.
-/
theorem ArticleInternalPairingFractionCertificate.exists_sequentialPairingPlan
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {elements : List (Interface.Element n)}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (certificate :
      ArticleInternalPairingFractionCertificate kinds elements
        (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0))
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections : List (List (External n)),
      SplayExecutionTranscript.BothPhaseSelections
          snapshot key transcript firstSelections secondSelections ∧
        firstSelections.flatten.Nodup ∧
        secondSelections.flatten.Nodup ∧
        ∀ group ∈ certificate.fraction.groups,
          ∃ firstSelection secondSelection winner firstLoser secondLoser
              candidates,
            firstSelection ∈ firstSelections ∧
              secondSelection ∈ secondSelections ∧
              firstSelection = [winner, firstLoser] ∧
              secondSelection = [winner, secondLoser] ∧
              Interface.Adjacent candidates winner firstLoser ∧
              Interface.Adjacent (candidates.erase firstLoser)
                winner secondLoser ∧
              firstLoser ≠ secondLoser ∧
              candidates.Perm [winner, firstLoser, secondLoser] ∧
              IsSegment candidates elements.reverse ∧
              Interface.Adjacent elements winner firstLoser ∧
              Interface.Adjacent (elements.erase firstLoser)
                winner secondLoser ∧
              winner ∈ elements ∧ firstLoser ∈ elements ∧
              secondLoser ∈ elements := by
  obtain ⟨firstSelections, secondSelections, joint, firstAligned,
      secondAligned, firstNodup, secondNodup⟩ :=
    transcript.exists_bothPhaseSelections_atDoubleGroups
      (Nat.le_refl n) key_lt_n rankZero
  refine ⟨firstSelections, secondSelections, joint, firstNodup, secondNodup,
    ?_⟩
  intro group groupMember
  exact certificate.exists_jointSelection_inside joint key_lt_n rankZero
    groupMember

/--
Kernel-checked form of the geometric content of
`lemma:internal-pairings-fraction`.

The side segment is the scheduler state immediately after the manuscript's
Step 2: `x⁻` and `x⁺` have been isolated, so the ambient list consists of the
proper-ancestor hit children only.  Cross-side unbrokenness promotes this
side segment to a segment of the full interleaved attachment order.  Reversal
then places it in chronological splay order, where complete four-child groups
give one internal pairing in each phase and leave at most six boundary
children.
-/
theorem article_internalPairingFractionCertificate
    {n key : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (block : Lazy.Block n)
    (ownerEq : block.owner = valuePos ⟨key, key_lt_n⟩)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before block)
    (sideSegment :
      IsSegment block.elements
        ((rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).elements.filter
          (fun element => decide
            (canonicalSide snapshot before element = block.side)))) :
    Nonempty
      (ArticleInternalPairingFractionCertificate kinds block.elements
        (rootHeavyPathChildrenBottomUp
          snapshot before (Nat.le_refl n) key 0)) := by
  rcases block with
    ⟨creator, owner, side, passCount, mode, elements, intervalGap⟩
  change owner = valuePos ⟨key, key_lt_n⟩ at ownerEq
  subst owner
  let block : Lazy.Block n := {
    creator := creator
    owner := valuePos ⟨key, key_lt_n⟩
    side := side
    passCount := passCount
    mode := mode
    elements := elements
    intervalGap := intervalGap
  }
  change canonicalBlockCrossSideUnbroken snapshot before block at unbroken
  change IsSegment block.elements
    ((rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).elements.filter
      (fun element => decide
        (canonicalSide snapshot before element = block.side))) at sideSegment
  change Nonempty
    (ArticleInternalPairingFractionCertificate kinds block.elements
      (rootHeavyPathChildrenBottomUp
        snapshot before (Nat.le_refl n) key 0))

  have fullTopDown :
      IsSegment block.elements
        (rootHeavyPathCanonicalChildOrder
          snapshot before key_lt_n rankZero).elements :=
    canonicalBlock_isSegment_childOrder
      (rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero)
      sideSegment unbroken

  have bottomUp :
      IsSegment block.elements.reverse
        (rootHeavyPathChildrenBottomUp
          snapshot before (Nat.le_refl n) key 0) := by
    simpa [rootHeavyPathCanonicalChildOrder,
      rootHeavyPathChildrenTopDown, rootHeavyPathChildrenBottomUp,
      rootHeavyPathEdgesBottomUp] using fullTopDown.reverse

  have everyElementHasSide :
      ∀ element ∈ block.elements.reverse,
        canonicalSide snapshot before element = block.side := by
    intro element reverseMember
    have member : element ∈ block.elements := by
      simpa only [List.mem_reverse] using reverseMember
    have filteredMember := sideSegment.mem member
    exact of_decide_eq_true (List.mem_filter.mp filteredMember).2

  obtain ⟨front, back, decomposition⟩ := bottomUp
  have uniform :=
    uniformSideInterval_of_decomposition
      (canonicalSide snapshot before) decomposition everyElementHasSide
  rw [map_canonicalSide_rootHeavyPathChildrenBottomUp
    snapshot before key_lt_n rankZero] at uniform
  have schedule := transcript.hitSideSchedule
  exact ⟨{
    fraction := schedule.internalPairingFractionWitness uniform
    front := front
    back := back
    decomposition := decomposition
    groups_eq := rfl
  }⟩

/--
End-to-end geometric form of the article lemma.  Starting from the isolated
unbroken lazy interval, it returns both the numerical fraction certificate
and the two concrete retained batches.  The batch methods above prove first
phase adjacency in `block.elements` and second phase adjacency after all
first losers have been removed.
-/
theorem article_internalPairingBatches
    {n key : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (block : Lazy.Block n)
    (ownerEq : block.owner = valuePos ⟨key, key_lt_n⟩)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before block)
    (sideSegment :
      IsSegment block.elements
        ((rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).elements.filter
          (fun element => decide
            (canonicalSide snapshot before element = block.side)))) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds block.elements
            (rootHeavyPathChildrenBottomUp
              snapshot before (Nat.le_refl n) key 0),
        ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key
          certificate.fraction.groups) := by
  obtain ⟨certificate⟩ :=
    article_internalPairingFractionCertificate snapshot transcript key_lt_n
      rankZero block ownerEq unbroken sideSegment
  obtain ⟨batches⟩ :=
    certificate.exists_retainedPairingBatches transcript key_lt_n rankZero
  exact ⟨⟨certificate, batches⟩⟩

/-- The numerical per-phase witness projected from the stronger certificate. -/
theorem article_internalPairingFractionWitness
    {n key : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (block : Lazy.Block n)
    (ownerEq : block.owner = valuePos ⟨key, key_lt_n⟩)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before block)
    (sideSegment :
      IsSegment block.elements
        ((rootHeavyPathCanonicalChildOrder snapshot before key_lt_n rankZero).elements.filter
          (fun element => decide
            (canonicalSide snapshot before element = block.side)))) :
    Nonempty (InternalPairingFractionWitness kinds block.elements.length) := by
  obtain ⟨certificate⟩ :=
    article_internalPairingFractionCertificate snapshot transcript key_lt_n
      rankZero block ownerEq unbroken sideSegment
  exact ⟨by simpa using certificate.fraction⟩

end Splay.Accounting
