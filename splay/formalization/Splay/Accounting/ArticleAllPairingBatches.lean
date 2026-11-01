import Splay.Accounting.ArticleInternalPairingFraction

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical

/-- Choose actual aligned rows for any subset of zig-zigs. No fraction or
unbroken-source premise is needed to enumerate the genuine endpoint pairs. -/
theorem ArticleRetainedPairingBatches.exists_of_groups
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
    Nonempty (ArticleRetainedPairingBatches snapshot before
      (Nat.le_refl n) key eligibleGroups) := by
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
  exact ⟨{
    rows := rows
    groups_perm := retainedGroupsPerm
    aligned := rowAligned
    firstEndpoints_nodup := retainedFirstNodup
    secondEndpoints_nodup := retainedSecondNodup
  }⟩


namespace ArticleRetainedPairingBatches

/-- Every actual zig-zig has one jointly aligned first/second row, including
rows that will require boundary moves or a source's first exempt passes. -/
theorem exists_all
    {n key : ℕ} {snapshot : Snapshot n} {before after : BST 0 n}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript : SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (key_lt_n : key < n) (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    Nonempty (ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key
      (zigZigDoubleGroupIndices kinds 0)) :=
  exists_of_groups transcript _ (zigZigDoubleGroupIndices_nodup kinds 0)
    (fun _ member => member) key_lt_n rankZero

/-- Keep literal rows of a frozen request, preserving both phase endpoints. -/
def filter {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before upper_le_n key groups)
    (keep : (ℕ × (List (External n) × List (External n))) → Bool) :
    ArticleRetainedPairingBatches snapshot before upper_le_n key
      ((batches.rows.filter keep).map Prod.fst) where
  rows := batches.rows.filter keep
  groups_perm := .refl _
  aligned := fun row member => batches.aligned row (List.mem_filter.mp member).1
  firstEndpoints_nodup :=
    (List.filter_sublist.flatMap
      (fun row : ℕ × (List (External n) × List (External n)) => row.2.1)).nodup batches.firstEndpoints_nodup
  secondEndpoints_nodup :=
    (List.filter_sublist.flatMap
      (fun row : ℕ × (List (External n) × List (External n)) => row.2.2)).nodup batches.secondEndpoints_nodup

theorem filtered_groups_nodup {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before : BST lower upper} {upper_le_n : upper ≤ n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before upper_le_n key groups)
    (distinct : groups.Nodup)
    (keep : (ℕ × (List (External n) × List (External n))) → Bool) :
    ((batches.rows.filter keep).map Prod.fst).Nodup :=
  (List.filter_sublist.map Prod.fst).nodup (batches.groups_perm.nodup_iff.mpr distinct)

end ArticleRetainedPairingBatches
end Splay.Accounting
