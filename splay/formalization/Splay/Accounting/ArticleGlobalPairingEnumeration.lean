import Splay.Accounting.ArticleGlobalPairingWorklist
import Splay.Accounting.ArticleInternalPairingExecution

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/-- A stable block identifier is ready when it is the source identifier of a
fully constructed article work item in the frozen state.  This predicate is
proof relevant: it retains the local fraction certificate, endpoint batches,
allocations, and outermost witnesses through the existential work item. -/
def ArticleReadySourceId
    {n : ℕ} (key : ℕ) (snapshot : Snapshot n) (before : BST 0 n)
    (kinds : List SplayStepKind) (params : Interface.Parameters)
    (state : Lazy.State n) (sourceId : Interface.BlockId) : Prop :=
  ∃ item :
      ArticleReadySourceWorkItem key snapshot before kinds params state,
    item.sourceId = sourceId

/-- Every ready source identifier is necessarily an actual block-list
position, because its chosen work item contains a successful source lookup. -/
theorem ArticleReadySourceId.lt_blocks_length
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n} {sourceId : Interface.BlockId}
    (ready :
      ArticleReadySourceId key snapshot before kinds params state sourceId) :
    sourceId < state.blocks.length := by
  obtain ⟨item, sourceEq⟩ := ready
  rw [← sourceEq]
  exact (List.getElem?_eq_some_iff.mp item.sourceFound).1

/-- The finite subtype of block-list positions which carry a ready source.
The range bound is included explicitly so that completeness is stated against
the persistent block list rather than an unbounded natural-number search. -/
noncomputable def articleReadySourceIndices
    {n : ℕ} (key : ℕ) (snapshot : Snapshot n) (before : BST 0 n)
    (kinds : List SplayStepKind) (params : Interface.Parameters)
    (state : Lazy.State n) :
    List { sourceId : Interface.BlockId //
      sourceId < state.blocks.length ∧
        ArticleReadySourceId key snapshot before kinds params state
          sourceId } := by
  classical
  exact (List.range state.blocks.length).filterMap fun sourceId =>
    if ready :
        ArticleReadySourceId key snapshot before kinds params state sourceId
    then some ⟨sourceId, ready.lt_blocks_length, ready⟩
    else none

/-- Choose the checked work item stored by one ready source index. -/
noncomputable def ArticleReadySourceIndex.item
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (index : { sourceId : Interface.BlockId //
      sourceId < state.blocks.length ∧
        ArticleReadySourceId key snapshot before kinds params state
          sourceId }) :
    ArticleReadySourceWorkItem key snapshot before kinds params state :=
  Classical.choose index.property.2

@[simp]
theorem ArticleReadySourceIndex.item_sourceId
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (index : { sourceId : Interface.BlockId //
      sourceId < state.blocks.length ∧
        ArticleReadySourceId key snapshot before kinds params state
          sourceId }) :
    (ArticleReadySourceIndex.item index).sourceId = index.1 :=
  Classical.choose_spec index.property.2

/-- Canonical finite worklist of every ready source in block-list order. -/
noncomputable def articleReadySourceWorklist
    {n : ℕ} (key : ℕ) (snapshot : Snapshot n) (before : BST 0 n)
    (kinds : List SplayStepKind) (params : Interface.Parameters)
    (state : Lazy.State n) :
    List (ArticleReadySourceWorkItem key snapshot before kinds params state) :=
  (articleReadySourceIndices key snapshot before kinds params state).map
    ArticleReadySourceIndex.item

namespace articleReadySourceIndices

/-- The finite enumerator contains precisely the in-range ready identifiers. -/
theorem mem_iff
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    {index : { sourceId : Interface.BlockId //
      sourceId < state.blocks.length ∧
        ArticleReadySourceId key snapshot before kinds params state
          sourceId }} :
    index ∈ articleReadySourceIndices key snapshot before kinds params state ↔
      ArticleReadySourceId key snapshot before kinds params state index.1 := by
  classical
  simp only [articleReadySourceIndices, List.mem_filterMap]
  constructor
  · intro member
    obtain ⟨sourceId, sourceMember, selected⟩ := member
    split at selected
    next ready => exact index.property.2
    next notReady => simp at selected
  · intro ready
    refine ⟨index.1, List.mem_range.mpr index.property.1, ?_⟩
    simp only [ready, dite_true]

/-- No source identifier occurs twice in the finite enumeration. -/
theorem nodup
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n} :
    (articleReadySourceIndices key snapshot before kinds params state).Nodup := by
  classical
  unfold articleReadySourceIndices
  apply List.Nodup.filterMap ?_ List.nodup_range
  intro first second output firstEq secondEq
  by_cases firstReady :
      ArticleReadySourceId key snapshot before kinds params state first
  · by_cases secondReady :
        ArticleReadySourceId key snapshot before kinds params state second
    · simp only [firstReady, secondReady, dite_true,
          Option.mem_some_iff] at firstEq secondEq
      have firstValue : first = output.1 :=
        congrArg Subtype.val firstEq
      have secondValue : second = output.1 :=
        congrArg Subtype.val secondEq
      exact firstValue.trans secondValue.symm
    · simp [secondReady] at secondEq
  · simp [firstReady] at firstEq

end articleReadySourceIndices

namespace articleReadySourceWorklist

/-- The worklist contains a representative for every ready in-range ID. -/
theorem complete
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    {sourceId : Interface.BlockId}
    (sourceLt : sourceId < state.blocks.length)
    (ready :
      ArticleReadySourceId key snapshot before kinds params state sourceId) :
    ∃ item ∈ articleReadySourceWorklist key snapshot before kinds params state,
      item.sourceId = sourceId := by
  classical
  let index : { sourceId : Interface.BlockId //
      sourceId < state.blocks.length ∧
        ArticleReadySourceId key snapshot before kinds params state
          sourceId } := ⟨sourceId, sourceLt, ready⟩
  have indexMember : index ∈
      articleReadySourceIndices key snapshot before kinds params state :=
    articleReadySourceIndices.mem_iff.mpr ready
  refine ⟨ArticleReadySourceIndex.item index, ?_,
    ArticleReadySourceIndex.item_sourceId index⟩
  exact List.mem_map.mpr ⟨index, indexMember, rfl⟩

/-- Every listed item still points to a block-list position of the frozen
state. -/
theorem sourceId_lt
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    {item : ArticleReadySourceWorkItem key snapshot before kinds params state}
    (member : item ∈
      articleReadySourceWorklist key snapshot before kinds params state) :
    item.sourceId < state.blocks.length := by
  obtain ⟨index, indexMember, itemEq⟩ := List.mem_map.mp member
  subst item
  rw [ArticleReadySourceIndex.item_sourceId index]
  exact index.property.1

/-- Stable source IDs are duplicate-free by construction, with no caller
supplied `Nodup` premise. -/
theorem ids_nodup
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n} :
    ((articleReadySourceWorklist key snapshot before kinds params state).map
      fun item => item.sourceId).Nodup := by
  classical
  unfold articleReadySourceWorklist
  rw [List.map_map]
  have indicesNodup := articleReadySourceIndices.nodup
    (key := key) (snapshot := snapshot) (before := before)
    (kinds := kinds) (params := params) (state := state)
  have valuesNodup := indicesNodup.map Subtype.val_injective
  have mappedEq :
      (articleReadySourceIndices key snapshot before kinds params state).map
          ((fun item => item.sourceId) ∘ ArticleReadySourceIndex.item) =
        (articleReadySourceIndices key snapshot before kinds params state).map
          Subtype.val := by
    apply List.map_congr_left
    intro index indexMember
    exact ArticleReadySourceIndex.item_sourceId index
  rw [mappedEq]
  exact valuesNodup

/-- Validity of the frozen state turns distinct source IDs into pairwise
disjoint source payloads. -/
theorem payloads_pairwise_disjoint
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (valid : state.Valid params) :
    ((articleReadySourceWorklist key snapshot before kinds params state).map
      fun item => item.source.elements).Pairwise List.Disjoint := by
  let items := articleReadySourceWorklist key snapshot before kinds params state
  have idsPairwise : items.Pairwise fun first second =>
      first.sourceId ≠ second.sourceId := by
    simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map] using
      (ids_nodup (key := key) (snapshot := snapshot) (before := before)
        (kinds := kinds) (params := params) (state := state))
  rw [List.pairwise_map]
  apply idsPairwise.imp
  intro first second idsNe
  simp only [List.disjoint_left]
  intro element firstMember secondMember
  apply idsNe
  exact valid.blockId_eq_of_element_mem
    first.sourceFound firstMember second.sourceFound secondMember

end articleReadySourceWorklist

/-- Execute every ready source in the frozen block-list order.  The only
semantic premises are the stable checkpoint, rank agreement, and the article
constant; finite enumeration, ID uniqueness, and source-payload separation are
all discharged internally. -/
theorem exists_completeReadySourceWorklistExecution
    {n : ℕ} {key : ℕ} {snapshot : Snapshot n} {before : BST 0 n}
    {kinds : List SplayStepKind} {params : Interface.Parameters}
    {state : Lazy.State n}
    (stable : state.Stable params)
    (rankEq : state.view.rank = snapshot.rank)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty (ArticleReadyWorklistExecution
      (articleReadySourceWorklist key snapshot before kinds params state)) := by
  apply ArticleReadyWorklistExecution.exists_of_ready
  · exact stable
  · exact rankEq
  · exact articleFraction
  · exact articleReadySourceWorklist.ids_nodup
  · exact articleReadySourceWorklist.payloads_pairwise_disjoint stable.valid

/-- Every unbroken non-boundary shrinking source in the canonical
post-isolation state has a complete dichotomy: either its certified internal
group list is empty, or its stable ID is ready for the global worklist.

This is the source-level coverage theorem which was previously only available
as a one-source execution statement.  Notice that it makes no arbitrary choice
of a worklist: readiness is a property of the frozen source ID. -/
theorem preparedCanonicalSource_empty_or_ready
    {n : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n} (key : Fin n)
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {leftId rightId : Interface.BlockId}
    {leftBlock rightBlock : Lazy.Block n}
    (leftFound : state.blocks[leftId]? = some leftBlock)
    (leftElements :
      leftBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).left])
    (rightFound : state.blocks[rightId]? = some rightBlock)
    (rightElements :
      rightBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).right])
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (ownerEq : source.owner = valuePos key)
    (sourceNeLeft : sourceId ≠ leftId)
    (sourceNeRight : sourceId ≠ rightId)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds source.elements
            (rootHeavyPathChildrenBottomUp snapshot before
              (Nat.le_refl n) key.val 0),
        { batches : ArticleRetainedPairingBatches snapshot before
            (Nat.le_refl n) key.val certificate.fraction.groups //
          certificate.fraction.groups = [] ∨
            ArticleReadySourceId key.val snapshot before kinds params state
              sourceId }) := by
  obtain ⟨⟨certificate, batches, _outcome⟩⟩ :=
    article_internalPairingExecution_of_preparedCanonicalBoundaries
      snapshot key transcript rankZero represents leftFound leftElements
      rightFound rightElements sourceFound sourceShrinking ownerEq
      sourceNeLeft sourceNeRight unbroken articleFraction
  refine ⟨⟨certificate, batches, ?_⟩⟩
  by_cases empty : certificate.fraction.groups = []
  · exact Or.inl empty
  · obtain ⟨item⟩ := ArticleReadySourceWorkItem.exists_of_certificate
      certificate batches empty represents.stable
      represents.nestedChildOrder sourceFound rfl sourceShrinking
    exact Or.inr ⟨item.1, item.2.1⟩

/-- Worklist-shaped form of `preparedCanonicalSource_empty_or_ready`: every
nonempty certified unbroken source occurs exactly where the finite enumerator
places its stable identifier. -/
theorem preparedCanonicalSource_empty_or_mem_worklist
    {n : ℕ} (snapshot : Snapshot n)
    {before after : BST 0 n} (key : Fin n)
    {execution : SplayExecution key.val before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key.val execution kinds zig zigZig zigZag)
    (rankZero : snapshot.rank (valuePos key) = 0)
    {params : Interface.Parameters} {state : Lazy.State n}
    (represents : state.Represents params snapshot before)
    {leftId rightId : Interface.BlockId}
    {leftBlock rightBlock : Lazy.Block n}
    (leftFound : state.blocks[leftId]? = some leftBlock)
    (leftElements :
      leftBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).left])
    (rightFound : state.blocks[rightId]? = some rightBlock)
    (rightElements :
      rightBlock.elements =
        [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
          snapshot before key).right])
    {sourceId : Interface.BlockId} {source : Lazy.Block n}
    (sourceFound : state.blocks[sourceId]? = some source)
    (sourceShrinking : source.mode = .shrinking)
    (ownerEq : source.owner = valuePos key)
    (sourceNeLeft : sourceId ≠ leftId)
    (sourceNeRight : sourceId ≠ rightId)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot before source)
    (articleFraction :
      10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty
      (Σ certificate :
          ArticleInternalPairingFractionCertificate kinds source.elements
            (rootHeavyPathChildrenBottomUp snapshot before
              (Nat.le_refl n) key.val 0),
        { batches : ArticleRetainedPairingBatches snapshot before
            (Nat.le_refl n) key.val certificate.fraction.groups //
          certificate.fraction.groups = [] ∨
            ∃ item ∈ articleReadySourceWorklist key.val snapshot before
                kinds params state,
              item.sourceId = sourceId }) := by
  obtain ⟨⟨certificate, batches, outcome⟩⟩ :=
    preparedCanonicalSource_empty_or_ready snapshot key transcript rankZero
      represents leftFound leftElements rightFound rightElements sourceFound
      sourceShrinking ownerEq sourceNeLeft sourceNeRight unbroken
      articleFraction
  refine ⟨⟨certificate, batches, ?_⟩⟩
  rcases outcome with empty | ready
  · exact Or.inl empty
  · exact Or.inr (articleReadySourceWorklist.complete
      (ready.lt_blocks_length) ready)

end Splay.Accounting
