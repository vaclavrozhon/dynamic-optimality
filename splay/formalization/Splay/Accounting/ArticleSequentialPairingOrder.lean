import Splay.Accounting.ArticleAllPairingBatches

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- If both losers enter the same side of their winner, the second one is
farther out. This concerns actual ternary branches, independently of lazy blocks. -/
def SequentialPairingOrder {n : ℕ} (winner first second : Interface.Element n) : Prop :=
  sideOf winner first = sideOf winner second →
    if sideOf winner second = .left then second.val < first.val else first.val < second.val

theorem HeapChildPairing.ofNode_sequentialOrder {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    SequentialPairingOrder (ofNode snapshot node .first).winner
      (ofNode snapshot node .first).loser (ofNode snapshot node .second).loser := by
  have left := AtNode.branchMin_in_branch snapshot node .left
  have middle := AtNode.branchMin_in_branch snapshot node .middle
  have right := AtNode.branchMin_in_branch snapshot node .right
  have owner := node.owner_eq_branchMin_heavy snapshot
  have lm : (node.branchMin snapshot .left).val < (node.branchMin snapshot .middle).val := by
    simp only [TernaryBranch.Contains] at left middle
    omega
  have mr : (node.branchMin snapshot .middle).val < (node.branchMin snapshot .right).val := by
    simp only [TernaryBranch.Contains] at middle right
    omega
  have lr := lm.trans mr
  unfold SequentialPairingOrder
  cases heavy : node.heavyBranch snapshot <;>
    simp [ofNode, owner, heavy, loserBranch, sideOf, lm, mr, lr,
      Nat.not_lt.mpr lm.le, Nat.not_lt.mpr mr.le, Nat.not_lt.mpr lr.le]

theorem ZigZigBothPairingEndpointsAt.sequentialOrder
    {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after winner firstLoser secondLoser) :
    SequentialPairingOrder winner firstLoser secondLoser := by
  induction both with
  | zigZigLeft a b c d upper => exact HeapChildPairing.ofNode_sequentialOrder snapshot _
  | zigZigRight a b c d upper second => exact HeapChildPairing.ofNode_sequentialOrder snapshot _
  | leftContext inside right ih => exact ih
  | rightContext left inside ih => exact ih

/-- A pair of literal phase selections retains the local order certificate. -/
def OrderedPhaseSelection {n : ℕ}
    (selections : List (External n) × List (External n)) : Prop :=
  ∃ winner first second, selections.1 = [winner, first] ∧
    selections.2 = [winner, second] ∧ SequentialPairingOrder winner first second

theorem SplayExecutionTranscript.BothPhaseSelections.ordered
    {n key lower upper : ℕ} {snapshot : Snapshot n} {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript : SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {firstSelections secondSelections : List (List (External n))}
    (joint : BothPhaseSelections snapshot key transcript firstSelections secondSelections) :
    ∀ selections ∈ firstSelections.zip secondSelections, OrderedPhaseSelection selections := by
  induction joint with
  | done root => simp
  | zig step tail tailTranscript rest ih => exact ih
  | zigZig step orientation tail tailTranscript endpoints rest ih =>
      intro selections member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, _, rfl, rfl, endpoints.sequentialOrder⟩
      · exact ih _ member
  | zigZag step orientation tail tailTranscript rest ih => exact ih

/-- Geometric order attached to the very same frozen rows as their alignment. -/
def ArticleRetainedPairingBatches.Ordered {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before upper_le_n key groups) : Prop :=
  ∀ row ∈ batches.rows, OrderedPhaseSelection row.2

theorem ArticleRetainedPairingBatches.Ordered.filter
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n} {groups : List ℕ}
    {batches : ArticleRetainedPairingBatches snapshot before upper_le_n key groups}
    (ordered : batches.Ordered)
    (keep : (ℕ × (List (External n) × List (External n))) → Bool) :
    (batches.filter keep).Ordered := by
  intro row member
  exact ordered row (List.mem_filter.mp member).1

/-- Construct all selected rows together with their actual two-phase order. -/
theorem ArticleRetainedPairingBatches.exists_ordered_of_groups
    {n key : ℕ} {snapshot : Snapshot n}
    {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (eligibleGroups : List ℕ)
    (eligibleNodup : eligibleGroups.Nodup)
    (eligibleSubset : eligibleGroups ⊆ zigZigDoubleGroupIndices kinds 0)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ batches : ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key eligibleGroups, batches.Ordered := by
  obtain ⟨firstSelections, secondSelections, joint, firstAligned,
      secondAligned, firstNodup, secondNodup⟩ :=
    transcript.exists_bothPhaseSelections_atDoubleGroups
      (Nat.le_refl n) key_lt_n rankZero
  let allGroups := zigZigDoubleGroupIndices kinds 0
  let selectionPairs := firstSelections.zip secondSelections
  let allRows := allGroups.zip selectionPairs
  let retainGroup : ℕ → Bool := fun group =>
    decide (group ∈ eligibleGroups)
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
          decide (group ∈ eligibleGroups) := by
    dsimp only [rows]
    rw [← List.filter_map]
    rw [allGroupProjection]
  have retainedGroupsNodup : (rows.map Prod.fst).Nodup := by
    rw [retainedGroupProjection]
    exact (zigZigDoubleGroupIndices_nodup kinds 0).filter _
  have retainedGroupsPerm :
      (rows.map Prod.fst).Perm eligibleGroups := by
    apply (List.perm_ext_iff_of_nodup retainedGroupsNodup
      eligibleNodup).mpr
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
  refine ⟨{
    rows := rows
    groups_perm := retainedGroupsPerm
    aligned := rowAligned
    firstEndpoints_nodup := retainedFirstNodup
    secondEndpoints_nodup := retainedSecondNodup
  }, ?_⟩
  intro row member
  have allMember : row ∈ allRows := (List.mem_filter.mp member).1
  have selectedMember : row.2 ∈ selectionPairs := (List.of_mem_zip allMember).2
  exact joint.ordered row.2 selectedMember


end Splay.Accounting
