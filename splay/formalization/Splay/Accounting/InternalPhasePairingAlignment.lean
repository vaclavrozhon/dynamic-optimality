import Splay.Accounting.SplayPairingsInParallel
import Splay.Accounting.InternalPairingFractionGeometry
import Splay.Accounting.RootHeavyPathFullOrder

namespace Splay.Accounting

open Splay.Rank
open Splay.Tree.BST
open SplayExecutionTranscript

/-- Global double-step indices occupied by zig-zigs, starting at `start`. -/
def zigZigDoubleGroupIndices : List SplayStepKind → ℕ → List ℕ
  | [], _ => []
  | .zig :: kinds, start => zigZigDoubleGroupIndices kinds start
  | .zigZig :: kinds, start =>
      start :: zigZigDoubleGroupIndices kinds (start + 1)
  | .zigZag :: kinds, start =>
      zigZigDoubleGroupIndices kinds (start + 1)

/-- A true transcript flag names a retained zig-zig global group. -/
theorem mem_zigZigDoubleGroupIndices_of_doubleStepFlags_eq_true
    {kinds : List SplayStepKind} {group start : ℕ}
    (flag : (doubleStepFlags kinds)[group]? = some true) :
    start + group ∈ zigZigDoubleGroupIndices kinds start := by
  induction kinds generalizing group start with
  | nil => simp [doubleStepFlags] at flag
  | cons kind kinds ih =>
      cases kind with
      | zig => simp [doubleStepFlags] at flag
      | zigZig =>
          cases group with
          | zero => simp [zigZigDoubleGroupIndices]
          | succ group =>
              have tailFlag :
                  (doubleStepFlags kinds)[group]? = some true := by
                simpa [doubleStepFlags] using flag
              have member := ih tailFlag (start := start + 1)
              simp only [zigZigDoubleGroupIndices, List.mem_cons]
              right
              have indexEq :
                  start + (group + 1) = start + 1 + group := by omega
              simpa only [indexEq] using member
      | zigZag =>
          cases group with
          | zero => simp [doubleStepFlags] at flag
          | succ group =>
              have tailFlag :
                  (doubleStepFlags kinds)[group]? = some true := by
                simpa [doubleStepFlags] using flag
              have member := ih tailFlag (start := start + 1)
              simp only [zigZigDoubleGroupIndices]
              have indexEq :
                  start + (group + 1) = start + 1 + group := by omega
              simpa only [indexEq] using member

/-- At offset zero, the flag index itself occurs in the aligned group list. -/
theorem mem_zigZigDoubleGroupIndices_zero_of_doubleStepFlags_eq_true
    {kinds : List SplayStepKind} {group : ℕ}
    (flag : (doubleStepFlags kinds)[group]? = some true) :
    group ∈ zigZigDoubleGroupIndices kinds 0 := by
  simpa using
    (mem_zigZigDoubleGroupIndices_of_doubleStepFlags_eq_true
      (start := 0) flag)

/-- Membership on the left of a `Forall₂` has a related right witness. -/
theorem forall₂_exists_right_of_mem_left
    {α β : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (aligned : List.Forall₂ relation left right)
    {item : α} (member : item ∈ left) :
    ∃ other, other ∈ right ∧ relation item other := by
  induction aligned with
  | nil => simp at member
  | @cons first second left right related rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · exact ⟨second, by simp, related⟩
      · obtain ⟨other, otherMember, otherRelated⟩ := ih tailMember
        exact ⟨other, by simp [otherMember], otherRelated⟩

/--
The retained two-node support groups are indexed by exactly the `true`
double-step positions.  This is the chronological indexing bridge between
the fraction argument and `PhaseSelections`.
-/
theorem HitSideSchedule.forall₂_doubleGroupIndices_zigZigHitGroups
    {kinds : List SplayStepKind} {sides : List Splay.Lazy.Side}
    (schedule : HitSideSchedule kinds sides)
    (remaining : List ℕ) (start : ℕ) :
    List.Forall₂
      (fun group support =>
        support = (remaining.drop (2 * group)).take 2)
      (zigZigDoubleGroupIndices kinds start)
      (zigZigHitGroups kinds (remaining.drop (2 * start))) := by
  induction schedule generalizing remaining start with
  | done =>
      simp [zigZigDoubleGroupIndices, zigZigHitGroups]
  | zig =>
      simp [zigZigDoubleGroupIndices, zigZigHitGroups]
  | zigZig tail ih =>
      apply List.Forall₂.cons
      · rfl
      · simpa [zigZigDoubleGroupIndices, zigZigHitGroups,
          List.drop_drop, show 2 * start + 2 = 2 * (start + 1) by omega]
          using ih remaining (start + 1)
  | zigZag opposite tail ih =>
      simpa [zigZigDoubleGroupIndices, zigZigHitGroups,
        List.drop_drop, show 2 * start + 2 = 2 * (start + 1) by omega]
        using ih remaining (start + 1)

/-- A phase endpoint pair supported at one global double-group index. -/
def PhaseSelectionSupportedAtDoubleGroup
    {n lower upper key : ℕ} (snapshot : Snapshot n)
    (before : BST lower upper) (upper_le_n : upper ≤ n)
    {after : BST lower upper}
    (execution : SplayExecution key before after)
    (group : ℕ) (children : List (External n)) : Prop :=
  HeapChildrenSupportedIn snapshot before upper_le_n
    ((execution.hitNodes.drop (2 * group)).take 2) children

/-- A supported endpoint lies in its ambient four-child double-group. -/
theorem PhaseSelectionSupportedAtDoubleGroup.mem_rootHeavyPathChildrenGroup
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper} {upper_le_n : upper ≤ n}
    {execution : SplayExecution key before after}
    {group : ℕ} {children : List (External n)}
    (supported :
      PhaseSelectionSupportedAtDoubleGroup
        snapshot before upper_le_n execution group children)
    (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {child : External n} (childMember : child ∈ children) :
    child ∈
      ((rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0).drop
        (4 * group)).take 4 := by
  obtain ⟨_, _, childSupported⟩ := supported
  obtain ⟨edge, treeMember, edgeChild, attachmentMember⟩ :=
    childSupported child childMember
  let cells :=
    rootHeavyPathCellsBottomUp snapshot before upper_le_n key 0
  have supportSublist :
      ((execution.hitNodes.drop (2 * group)).take 2).Sublist
        execution.hitNodes :=
    (List.take_sublist 2 (execution.hitNodes.drop (2 * group))).trans
      (List.drop_sublist (2 * group) execution.hitNodes)
  have attachmentAll : edge.attachmentKey ∈ execution.hitNodes :=
    supportSublist.mem attachmentMember
  have rawTopMember :
      edge ∈
        (rootHeavyPathCellsTopDown snapshot before upper_le_n key 0).flatMap
          RootHeavyPathCell.edges := by
    apply mem_rawRootHeavyPathEdgesTopDown_of_attachment_properAncestor
      snapshot before upper_le_n execution.key_bounds.1
        execution.key_bounds.2 0 treeMember
    simpa only [SplayExecution.hitNodes] using attachmentAll
  obtain ⟨cell, cellTopMember, edgeRawMember⟩ :=
    List.mem_flatMap.mp rawTopMember
  have cellBottomMember : cell ∈ cells := by
    simpa only [cells, rootHeavyPathCellsBottomUp, List.mem_reverse] using
      cellTopMember
  have edgeTopMember : edge ∈ cell.fullTopDownEdges :=
    cell.fullTopDownEdges_perm_edges.mem_iff.mpr edgeRawMember
  have edgeBottomMember : edge ∈ cell.fullBottomUpEdges := by
    simpa only [RootHeavyPathCell.fullBottomUpEdges, List.mem_reverse] using
      edgeTopMember
  have allMember :
      edge ∈ cells.flatMap RootHeavyPathCell.fullBottomUpEdges :=
    List.mem_flatMap.mpr ⟨cell, cellBottomMember, edgeBottomMember⟩
  have identities :
      cells.map RootHeavyPathCell.attachmentKey = execution.hitNodes := by
    simpa only [cells, SplayExecution.hitNodes] using
      map_attachmentKey_rootHeavyPathCellsBottomUp
        snapshot before upper_le_n execution.key_bounds.1
          execution.key_bounds.2 0
  have keysNodup :
      (cells.map RootHeavyPathCell.attachmentKey).Nodup := by
    rw [identities]
    exact execution.hitNodes_nodup
  have cellAttachment :
      ∀ current ∈ cells, ∀ currentEdge ∈ current.fullBottomUpEdges,
        currentEdge.attachmentKey = current.attachmentKey := by
    intro current currentMember currentEdge currentEdgeMember
    have currentTopMember : currentEdge ∈ current.fullTopDownEdges := by
      simpa only [RootHeavyPathCell.fullBottomUpEdges, List.mem_reverse] using
        currentEdgeMember
    have currentRawMember : currentEdge ∈ current.edges :=
      current.fullTopDownEdges_perm_edges.mem_iff.mp currentTopMember
    exact
      (rootHeavyPathCellsBottomUp_edge_geometry snapshot before upper_le_n
        execution.key_bounds.1 execution.key_bounds.2 key_lt_n rankZero 0
          current currentMember currentEdge currentRawMember).2.2
  have selectedKey :
      edge.attachmentKey ∈
        ((cells.drop (2 * group)).take 2).map
          RootHeavyPathCell.attachmentKey := by
    rw [List.map_take, List.map_drop, identities]
    exact attachmentMember
  have edgeSlice :
      edge ∈
        ((cells.drop (2 * group)).take 2).flatMap
          RootHeavyPathCell.fullBottomUpEdges :=
    mem_flatMap_slice_of_key RootHeavyPathCell.fullBottomUpEdges
      RootHeavyPathCell.attachmentKey (fun current => current.attachmentKey)
        cells (2 * group) 2 keysNodup cellAttachment allMember selectedKey
  have childSlice :
      child ∈
        ((cells.drop (2 * group)).take 2).flatMap
          (fun current => current.fullBottomUpEdges.map
            (fun edge => edge.child)) := by
    obtain ⟨current, currentMember, currentEdgeMember⟩ :=
      List.mem_flatMap.mp edgeSlice
    apply List.mem_flatMap.mpr
    refine ⟨current, currentMember, ?_⟩
    exact List.mem_map.mpr ⟨edge, currentEdgeMember, edgeChild⟩
  rw [rootHeavyPathChildrenBottomUp_groupChunk]
  exact childSlice

/-- Compose support-index alignment with support/endpoint alignment. -/
theorem forall₂_phaseSelectionSupportedAtDoubleGroup
    {n lower upper key : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper} {upper_le_n : upper ≤ n}
    {execution : SplayExecution key before after}
    {groups : List ℕ} {supports : List (List ℕ)}
    {selections : List (List (External n))}
    (indexed :
      List.Forall₂
        (fun group support =>
          support = (execution.hitNodes.drop (2 * group)).take 2)
        groups supports)
    (selected :
      List.Forall₂
        (HeapChildrenSupportedIn snapshot before upper_le_n)
        supports selections) :
    List.Forall₂
      (PhaseSelectionSupportedAtDoubleGroup
        snapshot before upper_le_n execution)
      groups selections := by
  induction indexed generalizing selections with
  | nil =>
      cases selected
      exact .nil
  | @cons group support groups supports supportEq rest ih =>
      cases selected with
      | cons headSelected tailSelected =>
          apply List.Forall₂.cons
          · simpa [PhaseSelectionSupportedAtDoubleGroup, supportEq] using
              headSelected
          · exact ih tailSelected

namespace SplayExecutionTranscript

/--
Choose the actual endpoints of either pairing phase, now aligned with their
global four-child double-group indices rather than only a compressed support
list.
-/
theorem exists_phaseSelections_atDoubleGroups
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (phase : PairingPhase) :
    ∃ selections : List (List (External n)),
      PhaseSelections snapshot phase key transcript selections ∧
        List.Forall₂
          (PhaseSelectionSupportedAtDoubleGroup
            snapshot before upper_le_n execution)
          (zigZigDoubleGroupIndices kinds 0) selections ∧
        selections.flatten.Nodup := by
  obtain ⟨selections, actual, supported⟩ :=
    transcript.exists_phaseSelections_supported
      upper_le_n key_lt_n rankZero phase
  have selectionsNodup : selections.flatten.Nodup :=
    HeapChildrenSupportedIn.flatten_nodup
      transcript.flatten_zigZigHitGroups_nodup supported
  have indexed :
      List.Forall₂
        (fun group support =>
          support = (execution.hitNodes.drop (2 * group)).take 2)
        (zigZigDoubleGroupIndices kinds 0) transcript.hitGroups := by
    simpa [SplayExecutionTranscript.hitGroups] using
      transcript.hitSideSchedule
        |>.forall₂_doubleGroupIndices_zigZigHitGroups execution.hitNodes 0
  exact ⟨selections, actual,
    forall₂_phaseSelectionSupportedAtDoubleGroup indexed supported,
    selectionsNodup⟩

/-- Both article phases aligned with the same global double-group indices. -/
theorem pairings_in_parallel_atDoubleGroups
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections : List (List (External n)),
      PhaseSelections snapshot .first key transcript firstSelections ∧
        PhaseSelections snapshot .second key transcript secondSelections ∧
        List.Forall₂
          (PhaseSelectionSupportedAtDoubleGroup
            snapshot before upper_le_n execution)
          (zigZigDoubleGroupIndices kinds 0) firstSelections ∧
        List.Forall₂
          (PhaseSelectionSupportedAtDoubleGroup
            snapshot before upper_le_n execution)
          (zigZigDoubleGroupIndices kinds 0) secondSelections ∧
        firstSelections.flatten.Nodup ∧
        secondSelections.flatten.Nodup := by
  obtain ⟨firstSelections, firstActual, firstAligned, firstNodup⟩ :=
    transcript.exists_phaseSelections_atDoubleGroups
      upper_le_n key_lt_n rankZero .first
  obtain ⟨secondSelections, secondActual, secondAligned, secondNodup⟩ :=
    transcript.exists_phaseSelections_atDoubleGroups
      upper_le_n key_lt_n rankZero .second
  exact ⟨firstSelections, secondSelections, firstActual, secondActual,
    firstAligned, secondAligned, firstNodup, secondNodup⟩

end SplayExecutionTranscript

end Splay.Accounting
