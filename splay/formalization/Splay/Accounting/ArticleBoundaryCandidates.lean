import Splay.Accounting.ArticleZigZigUniformSide
import Splay.Accounting.BoundaryCrossingCardinality
import Splay.Accounting.ArticleLargeSourceBoundaries
import Splay.Lazy.PartialBlockRelocation

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- The literal three children participating in a retained row, in the
original bottom-up order. The fourth child is the unpaired first child. -/
noncomputable def articleRowCandidates {n key : ℕ} (snapshot : Snapshot n) (before : BST 0 n)
    (row : ℕ × (List (External n) × List (External n))) : List (Element n) :=
  (((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0).drop (4 * row.1)).take 4).tail

theorem ArticleRetainedPairingBatches.mem_candidates_iff {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups)
    {row : ℕ × (List (External n) × List (External n))} (member : row ∈ batches.rows) {element : Element n} :
    element ∈ articleRowCandidates (key := key) snapshot before row ↔ element ∈ row.2.1 ++ row.2.2 := by
  obtain ⟨extra, winner, first, second, candidates, firstEq, secondEq, chunkEq,
    _, _, _, _, perm, _, _⟩ := batches.aligned row member
  simp only [articleRowCandidates, chunkEq, List.tail_cons, perm.mem_iff, firstEq, secondEq,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem ArticleRetainedPairingBatches.candidates_segment {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups)
    {row : ℕ × (List (External n) × List (External n))} (member : row ∈ batches.rows) :
    IsSegment (articleRowCandidates (key := key) snapshot before row)
      (rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0) := by
  obtain ⟨extra, winner, first, second, candidates, _, _, chunkEq, _⟩ := batches.aligned row member
  let whole := rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0
  refine ⟨whole.take (4 * row.1) ++ [extra], whole.drop (4 * row.1 + 4), ?_⟩
  have decomposition : whole = whole.take (4 * row.1) ++ (whole.drop (4 * row.1)).take 4 ++ whole.drop (4 * row.1 + 4) := by
    rw [← List.drop_drop]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  calc
    whole = _ := decomposition
    _ = _ := by simp only [whole, chunkEq, articleRowCandidates, List.tail_cons, List.append_assoc, List.singleton_append]

/-- Different retained candidate triples are disjoint even across phases. -/
theorem ArticleRetainedPairingBatches.candidates_disjoint {n key : ℕ} {snapshot : Snapshot n}
    {before : BST 0 n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups) (distinct : groups.Nodup)
    {first second : ℕ × (List (External n) × List (External n))}
    (firstMember : first ∈ batches.rows) (secondMember : second ∈ batches.rows) (different : first ≠ second) :
    List.Disjoint (articleRowCandidates (key := key) snapshot before first)
      (articleRowCandidates (key := key) snapshot before second) := by
  intro element inFirst inSecond
  exact List.disjoint_left.mp (batches.rows_endpoints_disjoint distinct firstMember secondMember different)
    ((batches.mem_candidates_iff firstMember).mp inFirst) ((batches.mem_candidates_iff secondMember).mp inSecond)

/-- The prepared source's proper-ancestor side word is an ordered list,
and a retained triple meeting this source lies on that same side. -/
theorem ArticleRequestPreparation.candidates_side_segment {n : ℕ} {params : Interface.Parameters}
    {snapshot : Snapshot n} {before after : BST 0 n} {key : Fin n} {initial : Lazy.State n}
    {kinds : List SplayStepKind} {execution : SplayExecution key.val before after} {zig zigZig zigZag : ℕ}
    (preparation : ArticleRequestPreparation params snapshot before key initial)
    (transcript : SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val (zigZigDoubleGroupIndices kinds 0))
    {id : Interface.BlockId} {source : Block n} (found : preparation.final.blocks[id]? = some source)
    {row : ℕ × (List (External n) × List (External n))} (member : row ∈ allBatches.rows)
    (meets : ∃ element ∈ row.2.1 ++ row.2.2, element ∈ source.elements) :
    IsSegment (articleRowCandidates (key := key.val) snapshot before row).reverse
      ((rootHeavyPathCanonicalChildOrder snapshot before key.isLt rankZero).elements.filter
        (fun element => decide (canonicalSide snapshot before element = source.side))) := by
  obtain ⟨side, uniform⟩ := allBatches.row_chunk_uniform transcript rankZero member
  obtain ⟨element, endpoint, inside⟩ := meets
  have sourceSide := (preparation.represents.valid.2 source (List.mem_of_getElem? found)).side_eq inside
  rw [preparation.represents.view_eq] at sourceSide
  have sideEq : side = source.side := (uniform element (allBatches.endpoint_mem_chunk member endpoint)).symm.trans sourceSide
  have segment := (allBatches.candidates_segment member).reverse
  have topDownSegment : IsSegment (articleRowCandidates (key := key.val) snapshot before row).reverse
      (rootHeavyPathCanonicalChildOrder snapshot before key.isLt rankZero).elements := by
    simpa only [rootHeavyPathCanonicalChildOrder, rootHeavyPathChildrenBottomUp, rootHeavyPathChildrenTopDown,
      rootHeavyPathEdgesBottomUp, List.map_reverse, List.reverse_reverse] using segment
  apply topDownSegment.filter_ambient
  intro child childMember
  apply decide_eq_true
  apply (uniform child ?_).trans sideEq
  apply allBatches.endpoint_mem_chunk member
  exact (allBatches.mem_candidates_iff member).mp (List.mem_reverse.mp childMember)

end Splay.Accounting
