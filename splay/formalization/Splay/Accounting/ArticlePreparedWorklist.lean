import Splay.Accounting.ArticleAdmissibleWorklist
import Splay.Accounting.ArticlePreparedSourceGeometry
import Splay.Accounting.ArticleSourceView

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST

namespace ArticleRequestPreparation

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
  (preparation : ArticleRequestPreparation params snapshot before key initial)
  {groups : List ℕ}
  (allBatches : ArticleRetainedPairingBatches snapshot before (Nat.le_refl n) key.val groups)

/-- The actual block at a bounded persistent index. -/
def locatedSource (index : Fin preparation.final.blocks.length) :
    ArticleLocatedSource preparation.final where
  id := index.val
  block := preparation.final.blocks[index.val]
  found := by simp

/-- The selected rows are exactly the original triples entirely inside this
source. The source can run both passes either by exemption or by size. -/
def SourceAdmissible (index : Fin preparation.final.blocks.length) : Prop :=
  let source := (preparation.locatedSource index).block
  source.owner = valuePos key ∧ source.mode = .shrinking ∧
    index.val ≠ preparation.leftId ∧ index.val ≠ preparation.rightId ∧
    (source.passCount + 1 < params.exemptPasses ∨
      params.matchingNumerator * source.elements.length ≤
        params.matchingDenominator *
          (ArticleSourcePairings.filtered source.elements allBatches).rows.length)

/-- Finite enumeration of every actual admissible source index. -/
noncomputable def admissibleIndices : Finset (Fin preparation.final.blocks.length) := by
  classical
  exact Finset.univ.filter (preparation.SourceAdmissible allBatches)

@[simp]
theorem mem_admissibleIndices (index : Fin preparation.final.blocks.length) :
    index ∈ preparation.admissibleIndices allBatches ↔
      preparation.SourceAdmissible allBatches index := by
  classical
  simp [admissibleIndices]

/-- Construct the actual allocations and geometry of one enumerated source,
retaining equality with its frozen rows. -/
noncomputable def admissibleItem
    (distinct : groups.Nodup)
    (rankZero : snapshot.rank (valuePos key) = 0)
    (index : { index : Fin preparation.final.blocks.length //
      index ∈ preparation.admissibleIndices allBatches }) :
    { item : ArticleAdmissibleSourceWorkItem key.val snapshot before params preparation.final //
      item.sourceId = index.val.val ∧
      item.source = (preparation.locatedSource index.val).block ∧
      item.batches.rows = (ArticleSourcePairings.filtered
        (preparation.locatedSource index.val).block.elements allBatches).rows } := by
  have eligible := (preparation.mem_admissibleIndices allBatches index.val).mp index.property
  obtain ⟨owner, shrinking, notLeft, notRight, admissible⟩ := eligible
  have sourceOrder := preparation.source_sublist rankZero
    (preparation.locatedSource index.val).found owner notLeft notRight
  have geometry := ArticleSourcePairings.filtered_valid _ allBatches distinct sourceOrder
  have admissible' :
      (preparation.locatedSource index.val).block.passCount + 1 < params.exemptPasses ∨
      params.matchingNumerator * (preparation.locatedSource index.val).block.elements.length ≤
        params.matchingDenominator *
          ((allBatches.rows.filter fun row => decide (∀ element ∈ row.2.1 ++ row.2.2,
            element ∈ (preparation.locatedSource index.val).block.elements)).map Prod.fst).length := by
    simpa [ArticleSourcePairings.filtered, ArticleRetainedPairingBatches.filter] using admissible
  exact Classical.choice (ArticleAdmissibleSourceWorkItem.exists_of_geometry geometry
    preparation.represents.stable preparation.represents.nestedChildOrder
    (preparation.locatedSource index.val).found rfl shrinking admissible')

/-- The concrete worklist uses each admissible persistent index once. -/
noncomputable def admissibleWorklist
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0) :
    List (ArticleAdmissibleSourceWorkItem key.val snapshot before params preparation.final) :=
  (preparation.admissibleIndices allBatches).attach.toList.map fun index =>
    (preparation.admissibleItem allBatches distinct rankZero index).val

@[simp]
theorem admissibleItem_sourceId
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)
    (index : { index : Fin preparation.final.blocks.length //
      index ∈ preparation.admissibleIndices allBatches }) :
    (preparation.admissibleItem allBatches distinct rankZero index).val.sourceId = index.val.val :=
  (preparation.admissibleItem allBatches distinct rankZero index).property.1

/-- No source is duplicated by the concrete enumerator. -/
theorem admissibleWorklist_ids_nodup
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0) :
    ((preparation.admissibleWorklist allBatches distinct rankZero).map
      fun item => item.sourceId).Nodup := by
  classical
  simp only [admissibleWorklist, List.map_map, Function.comp_def,
    admissibleItem_sourceId]
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro first second equal
  apply Subtype.ext
  exact Fin.ext equal

/-- Validity turns unique source indices into disjoint payloads. -/
theorem admissibleWorklist_payloads_disjoint
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0) :
    ((preparation.admissibleWorklist allBatches distinct rankZero).map
      fun item => item.source.elements).Pairwise List.Disjoint := by
  have ids := preparation.admissibleWorklist_ids_nodup allBatches distinct rankZero
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at ids
  rw [List.pairwise_map]
  apply ids.imp
  intro first second different
  rw [List.disjoint_left]
  intro element firstMember secondMember
  exact different (preparation.represents.valid.blockId_eq_of_element_mem
    first.sourceFound firstMember second.sourceFound secondMember)

/-- Every admissible source occurs with exactly its literal selected rows. -/
theorem admissibleWorklist_complete
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0)
    (index : Fin preparation.final.blocks.length)
    (admissible : preparation.SourceAdmissible allBatches index) :
    ∃ item ∈ preparation.admissibleWorklist allBatches distinct rankZero,
      item.sourceId = index.val ∧ item.source = (preparation.locatedSource index).block ∧
      item.batches.rows = (ArticleSourcePairings.filtered
        (preparation.locatedSource index).block.elements allBatches).rows := by
  classical
  let selected : { index : Fin preparation.final.blocks.length //
    index ∈ preparation.admissibleIndices allBatches } :=
    ⟨index, (preparation.mem_admissibleIndices allBatches index).mpr admissible⟩
  refine ⟨(preparation.admissibleItem allBatches distinct rankZero selected).val, ?_,
    (preparation.admissibleItem allBatches distinct rankZero selected).property⟩
  apply List.mem_map.mpr
  exact ⟨selected, by simp, rfl⟩

/-- Existence of the entire concrete admissible-source execution requires no
caller-supplied source list, allocation, or outermost-order witness. -/
theorem exists_admissibleWorklistExecution
    (distinct : groups.Nodup) (rankZero : snapshot.rank (valuePos key) = 0) :
    Nonempty (ArticleAdmissibleWorklistExecution
      (preparation.admissibleWorklist allBatches distinct rankZero)) := by
  exact ArticleAdmissibleWorklistExecution.exists_of_ready _ preparation.represents.stable
    preparation.represents.view_rank_eq
    (preparation.admissibleWorklist_ids_nodup allBatches distinct rankZero)
    (preparation.admissibleWorklist_payloads_disjoint allBatches distinct rankZero)

end ArticleRequestPreparation
end Splay.Accounting
