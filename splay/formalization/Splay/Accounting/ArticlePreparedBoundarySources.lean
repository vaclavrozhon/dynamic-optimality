import Splay.Accounting.ArticlePairingRowPartition
import Splay.Accounting.ArticleBoundaryBatch

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST
open ArticleBatchDestinationAllocation

namespace ArticleRequestPreparation

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
  (preparation : ArticleRequestPreparation params snapshot before key initial)

/-- Emptying the accessed owner's growing slots puts every actual root child
in a shrinking source, including the isolated boundary children. -/
theorem rootChild_shrinking {element : Interface.Element n}
    (parent : canonicalParent snapshot before element = some (valuePos key)) :
    ∃ (id : Interface.BlockId) (source : Lazy.Block n),
      preparation.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧ element ∈ source.elements := by
  have richParent : preparation.final.view.parent element = some (valuePos key) := by
    rw [preparation.represents.view_parent_eq]
    exact parent
  have assigned : element ∈ preparation.final.allElements :=
    (preparation.represents.complete element).mpr (by rw [richParent]; simp)
  obtain ⟨source, sourceMember, inside⟩ := State.mem_allElements_iff.mp assigned
  obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp sourceMember
  have ownerParent := (preparation.represents.valid.2 source sourceMember).parent_eq inside
  have owner : source.owner = valuePos key := Option.some.inj (ownerParent.symm.trans richParent)
  have shrinking : source.mode = .shrinking := by
    cases mode : source.mode with
    | shrinking => rfl
    | growing =>
        let index : Fin preparation.final.blocks.length := ⟨id, (List.getElem?_eq_some_iff.mp found).1⟩
        have getEq : preparation.final.blocks.get index = source := (List.getElem?_eq_some_iff.mp found).2
        have empty : source.elements = [] := by
          cases side : source.side with
          | left =>
              have result := preparation.accessedEmpty.1 index
              dsimp only at result
              rw [getEq] at result
              exact result mode owner side
          | right =>
              have result := preparation.accessedEmpty.2 index
              dsimp only at result
              rw [getEq] at result
              exact result mode owner side
        simp [empty] at inside
  exact ⟨id, source, found, shrinking, inside⟩

variable {groups : List ℕ}
  (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)
  (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)
  (execution : ArticleAdmissibleWorklistExecution
    (preparation.admissibleWorklist allBatches distinct rankZero))

/-- A boundary endpoint was not processed by any internal macro. -/
theorem boundaryEndpoint_not_internal
    {row : ℕ × (List (External n) × List (External n))}
    (rowMember : row ∈ (preparation.boundaryBatches allBatches distinct rankZero).rows)
    {element : Interface.Element n} (inside : element ∈ row.2.1 ++ row.2.2) :
    element ∉ execution.chain.matching.flatMap fun pairing => [pairing.winner, pairing.loser] := by
  intro processed
  have selected := (execution.endpoint_mem_iff element).mp processed
  obtain ⟨internal, internalMember, internalInside⟩ := List.mem_flatMap.mp selected
  exact List.disjoint_left.mp (preparation.boundaryRows_disjoint_internal allBatches distinct rankZero
    internalMember rowMember) internalInside inside

/-- Both endpoints of every remaining phase pair avoid all internal endpoints. -/
theorem boundaryPair_not_internal {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase
      (preparation.boundaryBatches allBatches distinct rankZero) matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    pairing.winner ∉ execution.chain.matching.flatMap (fun p => [p.winner, p.loser]) ∧
      pairing.loser ∉ execution.chain.matching.flatMap (fun p => [p.winner, p.loser]) := by
  obtain ⟨row, rowMember, selected⟩ := agreement.exists_row_of_mem member
  have result := fun element => preparation.boundaryEndpoint_not_internal allBatches distinct rankZero execution rowMember (element := element)
  cases phase with
  | first =>
      constructor <;> apply result _ <;> apply List.mem_append_left <;>
        simp only [articleRowSelection] at selected <;> rw [selected] <;> simp
  | second =>
      constructor <;> apply result _ <;> apply List.mem_append_right <;>
        simp only [articleRowSelection] at selected <;> rw [selected] <;> simp

/-- Every boundary loser has a constructed shrinking source at the actual
endpoint of the complete internal worklist. -/
theorem boundaryPair_shrinking {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase
      (preparation.boundaryBatches allBatches distinct rankZero) matching)
    {pairing : Interface.Pairing n} (member : pairing ∈ matching) :
    ∃ (id : Interface.BlockId) (source : Lazy.Block n),
      execution.chain.final.blocks[id]? = some source ∧ source.mode = .shrinking ∧ pairing.loser ∈ source.elements := by
  have boundaryDistinct := allBatches.filtered_groups_nodup distinct
    (fun row => decide (row ∉ preparation.internalRows allBatches distinct rankZero))
  have parents := agreement.root_parents boundaryDistinct key.isLt rankZero member
  obtain ⟨id, source, found, shrinking, inside⟩ := preparation.rootChild_shrinking parents.2
  apply execution.chain.shrinkingSource_of_not_loser found shrinking inside
  have notEndpoint := (preparation.boundaryPair_not_internal allBatches distinct rankZero execution agreement member).2
  intro leaves
  obtain ⟨batch, batchMember, loserMember⟩ := List.mem_flatMap.mp leaves
  obtain ⟨moved, movedMember, equal⟩ := List.mem_map.mp loserMember
  apply notEndpoint
  apply List.mem_flatMap.mpr
  exact ⟨moved, List.mem_flatMap.mpr ⟨batch, batchMember, movedMember⟩, by simp [equal]⟩

/-- The true internal reparenting preserves all boundary-pair outermost
inequalities because internal and boundary winners belong to different rows. -/
theorem boundaryPair_outermost {phase : PairingPhase} {matching : List (Interface.Pairing n)}
    (agreement : ArticleBatchEndpointAgreement phase
      (preparation.boundaryBatches allBatches distinct rankZero) matching) :
    BatchOutermostOrder execution.chain.final.view matching := by
  have boundaryDistinct := allBatches.filtered_groups_nodup distinct
    (fun row => decide (row ∉ preparation.internalRows allBatches distinct rankZero))
  have original := agreement.root_outermost boundaryDistinct key.isLt rankZero
  have atStart : BatchOutermostOrder preparation.final.view matching := by
    rw [preparation.represents.view_eq]
    exact original
  have payloads : execution.chain.batches.Pairwise
      (Function.onFun List.Disjoint ArticleSourceLoserBatch.sourceElements) := by
    have mapped : (execution.chain.batches.map ArticleSourceLoserBatch.sourceElements).Pairwise List.Disjoint := by
      rw [execution.batchSourceElements_eq]
      exact preparation.admissibleWorklist_payloads_disjoint allBatches distinct rankZero
    exact (List.pairwise_map (f := ArticleSourceLoserBatch.sourceElements)).mp mapped
  obtain ⟨afterView, viewEq⟩ := execution.chain.view_reparented payloads
  rw [← viewEq]
  apply afterView.outermostOrder_after_of_winners_ne atStart
  intro earlier earlierMember later laterMember equal
  have notEndpoint := (preparation.boundaryPair_not_internal allBatches distinct rankZero execution agreement laterMember).1
  apply notEndpoint
  exact List.mem_flatMap.mpr ⟨earlier, earlierMember, by simp [equal]⟩

end ArticleRequestPreparation
end Splay.Accounting
