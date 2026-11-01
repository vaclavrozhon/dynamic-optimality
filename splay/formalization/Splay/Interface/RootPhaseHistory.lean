import Splay.Interface.ConversionAccounting
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sigma

namespace Splay.Interface

/--
Every growing block is the root block of its own split lineage.

Split descendants are born shrinking, and no operation turns a shrinking
block back into a growing block.  This is the phase invariant used when the
u-shift incidence argument counts, at one time, root lineages with a fixed
creator by `growingLimit`.
-/
def GrowingIsLineageRoot {n : ℕ}
    (state : State n) (labels : RootLabels) : Prop :=
  ∀ blockId block,
    state.block? blockId = some block →
      block.mode = .growing →
      RootLabels.root? labels blockId = some blockId

/-- No block in the selected lineage is currently growing. -/
def NoGrowingInLineage {n : ℕ}
    (state : State n) (labels : RootLabels) (root : RootId) : Prop :=
  ∀ blockId block,
    state.block? blockId = some block →
      RootLabels.root? labels blockId = some root →
      block.mode ≠ .growing

theorem GrowingIsLineageRoot.noGrowingInLineage_of_root_shrinking
    {n : ℕ} {state : State n} {labels : RootLabels}
    (invariant : GrowingIsLineageRoot state labels)
    {root : RootId} {rootBlock : Block n}
    (rootFound : state.block? root = some rootBlock)
    (rootShrinking : rootBlock.mode = .shrinking) :
    NoGrowingInLineage state labels root := by
  intro blockId block blockFound labelFound blockGrowing
  have selfLabel := invariant blockId block blockFound blockGrowing
  have blockIdEq : blockId = root :=
    Option.some.inj (selfLabel.symm.trans labelFound)
  subst blockId
  rw [rootFound] at blockFound
  have blockEq : block = rootBlock :=
    Option.some.inj blockFound.symm
  subst block
  simp [rootShrinking] at blockGrowing

namespace State

/--
Distinct root IDs whose root blocks are growing with one fixed creator are
counted by `State.growingCount`.
-/
theorem roots_length_le_growingCount
    {n : ℕ} (state : State n) (creator : Element n)
    (roots : List RootId)
    (rootsNodup : roots.Nodup)
    (rootSpec :
      ∀ root ∈ roots,
        ∃ block,
          state.block? root = some block ∧
            block.mode = .growing ∧
            block.creator = creator) :
    roots.length ≤ state.growingCount creator := by
  let selected : List (Block n × ℕ) :=
    state.blocks.zipIdx.filter fun tagged =>
      decide
        (tagged.1.mode = .growing ∧
          tagged.1.creator = creator)
  let selectedIds : List ℕ :=
    selected.map Prod.snd
  have selectedIdsNodup : selectedIds.Nodup := by
    exact
      List.Nodup.sublist
        (List.Sublist.map Prod.snd List.filter_sublist)
        (List.nodup_zipIdx_map_snd state.blocks)
  have rootsSubset : roots ⊆ selectedIds := by
    intro root rootMem
    obtain ⟨block, blockFound, blockGrowing, blockCreator⟩ :=
      rootSpec root rootMem
    obtain ⟨rootLt, blockEq⟩ :=
      List.getElem?_eq_some_iff.mp blockFound
    have zipLt : root < state.blocks.zipIdx.length := by
      simpa using rootLt
    have zipGet :
        state.blocks.zipIdx[root] = (block, root) := by
      rw [List.getElem_zipIdx]
      simp [blockEq]
    have zipMem : (block, root) ∈ state.blocks.zipIdx := by
      simpa [zipGet] using
        List.getElem_mem (l := state.blocks.zipIdx) zipLt
    apply List.mem_map.mpr
    exact
      ⟨(block, root), by
        simp [selected, zipMem, blockGrowing, blockCreator],
        rfl⟩
  have rootsLength :
      roots.length ≤ selectedIds.length :=
    (rootsNodup.subperm rootsSubset).length_le
  have selectedLength :
      selectedIds.length =
        (state.blocks.filter fun block =>
          decide
            (block.mode = .growing ∧
              block.creator = creator)).length := by
    dsimp [selectedIds]
    rw [List.length_map]
    have filteredMap :
        (state.blocks.filter fun block =>
            decide
              (block.mode = .growing ∧
                block.creator = creator)) =
          (selected.map Prod.fst) := by
      rw [← List.zipIdx_map_fst 0 state.blocks,
        List.filter_map]
      rfl
    have lengths := congrArg List.length filteredMap
    simpa using lengths.symm
  rw [selectedLength] at rootsLength
  exact rootsLength

/-- The interface validity bound turns the preceding exact count into the
uniform `growingLimit` estimate used by u-shift incidence. -/
theorem roots_length_le_growingLimit
    {n : ℕ} {params : Parameters}
    {state : State n} (valid : state.Valid params)
    (creator : Element n) (roots : List RootId)
    (rootsNodup : roots.Nodup)
    (rootSpec :
      ∀ root ∈ roots,
        ∃ block,
          state.block? root = some block ∧
            block.mode = .growing ∧
            block.creator = creator) :
    roots.length ≤ params.growingLimit :=
  (state.roots_length_le_growingCount creator roots
      rootsNodup rootSpec).trans
    (valid.2.2 creator)

end State

private theorem growing_origin_modify
    {n : ℕ} (blocks : List (Block n)) (index : ℕ)
    (update : Block n → Block n)
    (preserves :
      ∀ block, (update block).mode = .growing →
        block.mode = .growing)
    {query : ℕ} {result : Block n}
    (found : (blocks.modify index update)[query]? = some result)
    (growing : result.mode = .growing) :
    ∃ original,
      blocks[query]? = some original ∧
        original.mode = .growing := by
  rw [List.getElem?_modify] at found
  cases originalFound : blocks[query]? with
  | none =>
      simp [originalFound] at found
  | some original =>
      by_cases same : index = query
      · simp [originalFound, same] at found
        subst result
        exact ⟨original, rfl, preserves original growing⟩
      · simp [originalFound, same] at found
        subst result
        exact ⟨original, rfl, growing⟩

private theorem growing_origin_insertAtDestinations
    {n : ℕ} (blocks : List (Block n))
    (matching : List (Pairing n))
    {query : ℕ} {result : Block n}
    (found :
      (insertAtDestinations blocks matching)[query]? = some result)
    (growing : result.mode = .growing) :
    ∃ original,
      blocks[query]? = some original ∧
        original.mode = .growing := by
  induction matching generalizing blocks with
  | nil =>
      exact ⟨result, found, growing⟩
  | cons pairing matching ih =>
      let modified :=
        blocks.modify pairing.destination fun destination =>
          { destination with
            elements := pairing.loser :: destination.elements }
      have foundTail :
          (insertAtDestinations modified matching)[query]? =
            some result := by
        exact found
      obtain ⟨updated, updatedFound, updatedGrowing⟩ :=
        ih modified foundTail
      exact
        growing_origin_modify blocks pairing.destination
          (fun destination =>
            { destination with
              elements := pairing.loser :: destination.elements })
          (by
            intro destination destinationGrowing
            exact destinationGrowing)
          updatedFound updatedGrowing

private theorem growing_origin_modify_fixed
    {n : ℕ} (blocks : List (Block n)) (index : ℕ)
    (source replacement : Block n)
    (sourceFound : blocks[index]? = some source)
    (replacementGrowing :
      replacement.mode = .growing → source.mode = .growing)
    {query : ℕ} {result : Block n}
    (found :
      (blocks.modify index fun _ => replacement)[query]? =
        some result)
    (growing : result.mode = .growing) :
    ∃ original,
      blocks[query]? = some original ∧
        original.mode = .growing := by
  rw [List.getElem?_modify] at found
  cases originalFound : blocks[query]? with
  | none =>
      simp [originalFound] at found
  | some original =>
      by_cases same : index = query
      · subst query
        rw [sourceFound] at originalFound
        have originalEq : original = source :=
          Option.some.inj originalFound.symm
        subst original
        simp [sourceFound] at found
        subst result
        exact ⟨source, rfl, replacementGrowing growing⟩
      · simp [originalFound, same] at found
        subst result
        exact ⟨original, rfl, growing⟩

private theorem root?_after_old
    {n : ℕ} (labels : RootLabels) (operation : Operation n)
    {blockId : BlockId} (old : blockId < labels.length) :
    RootLabels.root? (RootLabels.after labels operation) blockId =
      RootLabels.root? labels blockId := by
  cases operation <;>
    simp [RootLabels.after, RootLabels.root?,
      List.getElem?_append_left old]

namespace GrowingIsLineageRoot

/-- The phase invariant is preserved by one aligned legal operation. -/
theorem after_step
    {n : ℕ} {params : Parameters}
    {before after : State n} {labels : RootLabels}
    {operation : Operation n}
    (invariant : GrowingIsLineageRoot before labels)
    (aligned : labels.length = before.blocks.length)
    (step : Step params before operation after) :
    GrowingIsLineageRoot after
      (RootLabels.after labels operation) := by
  intro query result found growing
  have oldRoot
      {original : Block n}
      (originalFound : before.block? query = some original)
      (originalGrowing : original.mode = .growing) :
      RootLabels.root?
          (RootLabels.after labels operation) query =
        some query := by
    have queryLt : query < before.blocks.length :=
      (List.getElem?_eq_some_iff.mp originalFound).choose
    rw [root?_after_old labels operation (by simpa [aligned] using queryLt)]
    exact invariant query original originalFound originalGrowing
  unfold State.block? at found
  cases effectEq : step.2.1 with
  | convert sourceFound sourceGrowing blocksEq valuesEq =>
      rw [blocksEq] at found
      obtain ⟨original, originalFound, originalGrowing⟩ :=
        growing_origin_modify before.blocks _ _
          (by
            intro source convertedGrowing
            simp at convertedGrowing)
          found growing
      exact oldRoot originalFound originalGrowing
  | create room blocksEq valuesEq =>
      rename_i creator
      rw [blocksEq, List.getElem?_append] at found
      by_cases old : query < before.blocks.length
      · simp only [old, if_pos] at found
        exact oldRoot found growing
      · simp only [old] at found
        have offsetLt :
            query - before.blocks.length < 1 :=
          (List.getElem?_eq_some_iff.mp found).choose
        have offsetZero : query - before.blocks.length = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ offsetLt)
        have queryEq : query = before.blocks.length := by
          exact
            Nat.le_antisymm
              (Nat.sub_eq_zero_iff_le.mp offsetZero)
              (Nat.le_of_not_gt old)
        subst query
        simpa [aligned] using
          RootLabels.create_root? (n := n) labels creator
  | insert targetFound targetGrowing unassigned valueOrder
      blocksEq valuesEq =>
      rw [blocksEq] at found
      obtain ⟨original, originalFound, originalGrowing⟩ :=
        growing_origin_modify before.blocks _ _
          (by
            intro target targetStillGrowing
            exact targetStillGrowing)
          found growing
      exact oldRoot originalFound originalGrowing
  | delete sourceFound sourceShrinking present blocksEq valuesEq =>
      rw [blocksEq] at found
      obtain ⟨original, originalFound, originalGrowing⟩ :=
        growing_origin_modify before.blocks _ _
          (by
            intro source sourceStillGrowing
            exact sourceStillGrowing)
          found growing
      exact oldRoot originalFound originalGrowing
  | pass sourceFound validMatching blocksEq valuesEq =>
      rename_i sourceId source matching
      rw [blocksEq] at found
      unfold passBlocks at found
      obtain ⟨updated, updatedFound, updatedGrowing⟩ :=
        growing_origin_insertAtDestinations
          (before.blocks.modify sourceId fun _ =>
            { source with
              passCount := source.passCount + 1
              elements := removeLosers source.elements matching })
          matching found growing
      obtain ⟨original, originalFound, originalGrowing⟩ :=
        growing_origin_modify_fixed before.blocks sourceId source
          { source with
            passCount := source.passCount + 1
            elements := removeLosers source.elements matching }
          (by simpa [State.block?] using sourceFound)
          (by
            intro sourceAfterGrowing
            exact sourceAfterGrowing)
          updatedFound updatedGrowing
      exact oldRoot originalFound originalGrowing
  | split sourceFound sourceShrinking prefixLe blocksEq valuesEq =>
      rename_i sourceId source prefixLength
      rw [blocksEq] at found
      unfold splitBlocks at found
      rw [List.getElem?_append] at found
      by_cases old :
          query <
            (before.blocks.modify sourceId fun current =>
              { current with elements := [] }).length
      · simp only [old, if_pos] at found
        obtain ⟨original, originalFound, originalGrowing⟩ :=
          growing_origin_modify before.blocks sourceId _
            (by
              intro oldSource sourceAfterGrowing
              exact sourceAfterGrowing)
            found growing
        exact oldRoot originalFound originalGrowing
      · simp only [old] at found
        simp only [List.length_modify] at found
        have offsetLt :
            query - before.blocks.length < 2 :=
          (List.getElem?_eq_some_iff.mp found).choose
        have offsetCases :
            query - before.blocks.length = 0 ∨
              query - before.blocks.length = 1 :=
          Nat.le_one_iff_eq_zero_or_eq_one.mp
            (Nat.le_of_lt_succ offsetLt)
        rcases offsetCases with offset | offset <;>
          simp [offset] at found <;>
          subst result <;>
          simp [sourceShrinking] at growing
  | decrease canDecrease blocksEq valuesEq =>
      exact oldRoot (by simpa [State.block?, blocksEq] using found) growing
  | increase canIncrease blocksEq valuesEq =>
      exact oldRoot (by simpa [State.block?, blocksEq] using found) growing

end GrowingIsLineageRoot

namespace HistoryTrace

/-- The phase invariant holds at every endpoint of an initial history. -/
theorem growingIsLineageRoot
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {initialLabels finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial initialLabels operations final finalLabels)
    (aligned : initialLabels.length = initial.blocks.length)
    (invariant : GrowingIsLineageRoot initial initialLabels) :
    GrowingIsLineageRoot final finalLabels := by
  induction history with
  | nil valid =>
      exact invariant
  | @cons before middle after beforeLabels afterLabels operation operations
      head tail ih =>
      have nextAligned :
          (RootLabels.after beforeLabels operation).length =
            middle.blocks.length :=
        (HistoryStep.mk head rfl).labels_length aligned
      exact
        ih nextAligned
          (invariant.after_step aligned head)

/-- In particular, every history lifted from the empty-block initial state
has the phase invariant at its endpoint. -/
theorem growingIsLineageRoot_of_initial
    {n : ℕ} {params : Parameters}
    {initial final : State n}
    {finalLabels : RootLabels}
    {operations : List (Operation n)}
    (history :
      HistoryTrace params initial [] operations final finalLabels)
    (initialState : initial.Initial params) :
    GrowingIsLineageRoot final finalLabels := by
  apply history.growingIsLineageRoot
  · simp [initialState.2]
  · intro blockId block found
    simp [State.block?, initialState.2] at found

end HistoryTrace

end Splay.Interface
