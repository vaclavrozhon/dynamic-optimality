import Splay.Accounting.ArticlePreparedWorklist
import Splay.Accounting.ArticleRootPairingGeometry

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST

/-- Every endpoint remains inside its original four-child group. -/
theorem ArticleRetainedPairingBatches.endpoint_mem_chunk
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups)
    {row : ℕ × (List (External n) × List (External n))} (member : row ∈ batches.rows)
    {element : External n} (inside : element ∈ row.2.1 ++ row.2.2) :
    element ∈ ((rootHeavyPathChildrenBottomUp snapshot before (Nat.le_refl n) key 0).drop
      (4 * row.1)).take 4 := by
  obtain ⟨extra, winner, first, second, candidates, firstEq, secondEq,
    chunkEq, _, _, _, _, perm, _, _⟩ := batches.aligned row member
  rw [chunkEq]
  apply List.mem_cons_of_mem
  apply perm.mem_iff.mpr
  rw [firstEq, secondEq] at inside
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside ⊢
  tauto

/-- Distinct frozen rows cannot share any endpoint across either phase. -/
theorem ArticleRetainedPairingBatches.rows_endpoints_disjoint
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {groups : List ℕ}
    (batches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key groups)
    (distinct : groups.Nodup)
    {first second : ℕ × (List (External n) × List (External n))}
    (firstMember : first ∈ batches.rows) (secondMember : second ∈ batches.rows)
    (different : first ≠ second) :
    List.Disjoint (first.2.1 ++ first.2.2) (second.2.1 ++ second.2.2) := by
  have groupNe : first.1 ≠ second.1 := by
    intro equal
    exact different (List.inj_on_of_nodup_map (batches.groups_perm.nodup_iff.mpr distinct)
      firstMember secondMember equal)
  rw [List.disjoint_left]
  intro element inFirst inSecond
  exact groupChunks_disjoint_of_nodup (rootHeavyPathChildrenBottomUp_nodup snapshot before)
    groupNe (batches.endpoint_mem_chunk firstMember inFirst) (batches.endpoint_mem_chunk secondMember inSecond)

namespace ArticleRequestPreparation

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
  (preparation : ArticleRequestPreparation params snapshot before key initial)
  {groups : List ℕ}
  (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)
  (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)

/-- All rows selected for the actual internal source worklist. -/
noncomputable def internalRows : List (ℕ × (List (External n) × List (External n))) :=
  (preparation.admissibleWorklist allBatches distinct rankZero).flatMap fun item => item.batches.rows

/-- The exact complement of internal rows is sent to boundary implementation. -/
noncomputable def boundaryBatches :=
  allBatches.filter fun row => decide (row ∉ preparation.internalRows allBatches distinct rankZero)

theorem internalRows_subset : preparation.internalRows allBatches distinct rankZero ⊆ allBatches.rows := by
  intro row member
  obtain ⟨item, itemMember, rowMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, indexMember, itemEq⟩ := List.mem_map.mp itemMember
  subst item
  have rowsEq := (preparation.admissibleItem allBatches distinct rankZero index).property.2.2
  rw [rowsEq] at rowMember
  exact (List.mem_filter.mp rowMember).1

/-- Literal row partition, with no inferred coverage premise. -/
theorem mem_boundaryBatches (row : ℕ × (List (External n) × List (External n))) :
    row ∈ (preparation.boundaryBatches allBatches distinct rankZero).rows ↔
      row ∈ allBatches.rows ∧ row ∉ preparation.internalRows allBatches distinct rankZero := by
  simp [boundaryBatches, ArticleRetainedPairingBatches.filter]

theorem boundaryRows_disjoint_internal
    {internal boundary : ℕ × (List (External n) × List (External n))}
    (internalMember : internal ∈ preparation.internalRows allBatches distinct rankZero)
    (boundaryMember : boundary ∈ (preparation.boundaryBatches allBatches distinct rankZero).rows) :
    List.Disjoint (internal.2.1 ++ internal.2.2) (boundary.2.1 ++ boundary.2.2) := by
  have selected := (preparation.mem_boundaryBatches allBatches distinct rankZero boundary).mp boundaryMember
  apply allBatches.rows_endpoints_disjoint distinct
    (preparation.internalRows_subset allBatches distinct rankZero internalMember) selected.1
  intro equal
  exact selected.2 (equal ▸ internalMember)

end ArticleRequestPreparation

/-- Membership in the executed chain's endpoint list is exactly membership
in the frozen rows. The two phases may have different interleavings. -/
theorem ArticleAdmissibleWorklistExecution.endpoint_mem_iff
    {n key : ℕ} {snapshot : Snapshot n} {before : BST 0 n} {params : Interface.Parameters}
    {state : Lazy.State n}
    {items : List (ArticleAdmissibleSourceWorkItem key snapshot before params state)}
    (execution : ArticleAdmissibleWorklistExecution items) (element : Interface.Element n) :
    element ∈ execution.chain.matching.flatMap (fun pairing => [pairing.winner, pairing.loser]) ↔
      element ∈ (items.flatMap fun item => item.batches.rows).flatMap fun row => row.2.1 ++ row.2.2 := by
  have equal := congrArg (fun pairs : List (List (Interface.Element n) × List (Interface.Element n)) =>
    pairs.flatMap fun pair => pair.1 ++ pair.2) execution.batchEndpoints_eq
  simp only [List.flatMap_map, Function.comp_def] at equal
  simp only [ArticleSourceMacroChain.matching, List.flatMap_assoc, List.flatMap_append]
  rw [equal]
  simp only [List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨item, itemMember, first | second⟩
    · obtain ⟨row, rowMember, inside⟩ := first
      exact ⟨item, itemMember, row, rowMember, Or.inl inside⟩
    · obtain ⟨row, rowMember, inside⟩ := second
      exact ⟨item, itemMember, row, rowMember, Or.inr inside⟩
  · rintro ⟨item, itemMember, row, rowMember, first | second⟩
    · exact ⟨item, itemMember, Or.inl ⟨row, rowMember, first⟩⟩
    · exact ⟨item, itemMember, Or.inr ⟨row, rowMember, second⟩⟩

end Splay.Accounting
