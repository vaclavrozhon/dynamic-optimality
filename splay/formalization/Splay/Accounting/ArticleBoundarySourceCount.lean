import Splay.Accounting.ArticleBoundaryCandidates

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- Rows with at least one original endpoint in a given source interval. -/
noncomputable def articleRowsTouching {n : ℕ}
    (rows : List (ℕ × (List (External n) × List (External n)))) (elements : List (Element n)) :=
  rows.filter (fun row => decide (∃ element ∈ row.2.1 ++ row.2.2, element ∈ elements))

/-- An admissible source meets at most two genuine boundary rows, hence at
most four boundary pairings during the request. Broken first-splay sources
are included: only contiguity on their own side is used. -/
theorem ArticleRequestPreparation.boundaryRows_touching_source_le_two {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before after : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    {kinds : List SplayStepKind} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val (zigZigDoubleGroupIndices kinds 0))
    {id : Interface.BlockId} {source : Block n} (found : preparation.final.blocks[id]? = some source)
    (owner : source.owner = valuePos key) (notLeft : id ≠ preparation.leftId) (notRight : id ≠ preparation.rightId)
    (nonempty : source.elements ≠ [])
    (admissible : preparation.SourceAdmissible allBatches ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩) :
    (articleRowsTouching (preparation.boundaryBatches allBatches (zigZigDoubleGroupIndices_nodup kinds 0) rankZero).rows
      source.elements).length ≤ 2 := by
  classical
  let distinct := zigZigDoubleGroupIndices_nodup kinds 0
  let boundary := preparation.boundaryBatches allBatches distinct rankZero
  let selected := articleRowsTouching boundary.rows source.elements
  let whole := (rootHeavyPathCanonicalChildOrder snapshot before key.isLt rankZero).elements.filter
    (fun element => decide (canonicalSide snapshot before element = source.side))
  have selectedSpec : ∀ row ∈ selected, row ∈ boundary.rows ∧ row ∈ allBatches.rows ∧
      ∃ element ∈ row.2.1 ++ row.2.2, element ∈ source.elements := by
    intro row member
    have selection := List.mem_filter.mp member
    exact ⟨selection.1, ((preparation.mem_boundaryBatches allBatches distinct rankZero row).mp selection.1).1,
      of_decide_eq_true selection.2⟩
  have rowsNodup : allBatches.rows.Nodup := (allBatches.groups_perm.nodup_iff.mpr distinct).of_map
  have boundaryNodup : boundary.rows.Nodup := rowsNodup.filter _
  have selectedNodup : selected.Nodup := boundaryNodup.filter _
  obtain ⟨removed, erased, fresh⟩ := exists_articleIsolatedBoundariesWitness snapshot before key rankZero
    preparation.represents preparation.leftFound preparation.leftElements
    preparation.rightFound preparation.rightElements found owner notLeft notRight
  have sourceSegment : IsSegment source.elements whole := by
    rw [show whole = _ from erased]
    exact (preparation.represents.valid.2 source (List.mem_of_getElem? found)).isSegment.foldl_erase_ambient_of_fresh fresh
  have ordered : whole.Pairwise (fun a b => match source.side with | .left => a.val < b.val | .right => b.val < a.val) := by
    rw [show whole = _ from erased]
    apply List.Pairwise.foldl_erase
    cases side : source.side with
    | left => exact ((preparation.final.view.topDown_ordered source.owner).1.filter _)
    | right => exact ((preparation.final.view.topDown_ordered source.owner).2.filter _)
  have count := crossing_segments_card_le_two selected.toFinset
    (fun row => (articleRowCandidates (key := key.val) snapshot before row).reverse) nonempty sourceSegment source.side ordered
    (by
      intro row member
      have selected := selectedSpec row (List.mem_toFinset.mp member)
      exact preparation.candidates_side_segment transcript rankZero allBatches found selected.2.1 selected.2.2)
    (by
      intro first firstMember second secondMember different
      have firstSpec := selectedSpec first (List.mem_toFinset.mp firstMember)
      have secondSpec := selectedSpec second (List.mem_toFinset.mp secondMember)
      intro element inFirst inSecond
      exact List.disjoint_left.mp (allBatches.candidates_disjoint distinct firstSpec.2.1 secondSpec.2.1 different)
        (List.mem_reverse.mp inFirst) (List.mem_reverse.mp inSecond))
    (by
      intro row member
      have selected := selectedSpec row (List.mem_toFinset.mp member)
      obtain ⟨inside, endpoint, insideSource⟩ := selected.2.2
      have notContained := preparation.boundaryRow_not_contained_of_admissible allBatches distinct rankZero
        ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩ admissible selected.1
      have blockEq : (preparation.locatedSource ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩).block = source :=
        (List.getElem?_eq_some_iff.mp found).2
      rw [blockEq] at notContained
      push_neg at notContained
      obtain ⟨outside, outsideEndpoint, outsideSource⟩ := notContained
      exact ⟨inside, List.mem_reverse.mpr ((allBatches.mem_candidates_iff selected.2.1).mpr endpoint), insideSource,
        outside, List.mem_reverse.mpr ((allBatches.mem_candidates_iff selected.2.1).mpr outsideEndpoint), outsideSource⟩)
  simpa only [List.toFinset_card_of_nodup selectedNodup] using count

end Splay.Accounting
