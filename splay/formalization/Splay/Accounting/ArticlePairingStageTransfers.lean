import Splay.Accounting.ArticlePairingStageBoundaryGeometry
import Splay.Lazy.TwoSideTransfer

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- A growing block of an owner which never wins survives the complete
internal source worklist literally, including its empty payload. -/
theorem ArticleSourceMacroChain.preservesGrowingBlock {n : ℕ} {params : Interface.Parameters}
    {initial : Lazy.State n} (chain : ArticleSourceMacroChain params initial)
    {id : Interface.BlockId} {block : Lazy.Block n}
    (found : initial.blocks[id]? = some block) (growing : block.mode = .growing)
    (notWinner : ∀ pairing ∈ chain.matching, pairing.winner ≠ block.owner) :
    chain.final.blocks[id]? = some block := by
  induction chain with
  | nil => exact found
  | cons head tail ih =>
      apply ih (head.preservesGrowingBlock found growing (by
        intro pairing member
        exact notWinner pairing (List.mem_append_left _ member)))
      intro pairing member
      exact notWinner pairing (List.mem_append_right _ member)

namespace ArticlePairingStage

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
  (stage : ArticlePairingStage params snapshot before key kinds initial)

/-- The two actual boundary phases preserve every growing block whose owner
never wins, after the same exact preservation by the internal chain. -/
theorem preservesGrowingBlock {id : Interface.BlockId} {block : Lazy.Block n}
    (found : stage.preparation.final.blocks[id]? = some block) (growing : block.mode = .growing)
    (notWinner : ∀ pairing ∈ stage.matching, pairing.winner ≠ block.owner) :
    stage.final.blocks[id]? = some block := by
  have internalFound := stage.internal.chain.preservesGrowingBlock found growing
    (fun pairing member => notWinner pairing (List.mem_append_left _ member))
  have firstFound := stage.boundary.first.preservesGrowingBlock internalFound growing
    (fun pairing member => notWinner pairing (List.mem_append_right _ (List.mem_append_left _ member)))
  exact stage.boundary.second.preservesGrowingBlock firstFound growing
    (fun pairing member => notWinner pairing (List.mem_append_right _ (List.mem_append_right _ member)))

/-- An empty growing slot stays empty whenever its owner never wins. Stable
uniqueness connects the preserved original ID to any queried final slot. -/
theorem growingEmptyAt (owner : Element n) (side : Side)
    (empty : ArticleGrowingEmptyAt stage.preparation.final owner side)
    (notWinner : ∀ pairing ∈ stage.matching, pairing.winner ≠ owner) :
    ArticleGrowingEmptyAt stage.final owner side := by
  intro id
  dsimp only
  intro growing ownerEq sideEq
  let block := stage.final.blocks.get id
  have found : stage.final.blocks[id.val]? = some block := by simp [block]
  obtain ⟨oldId, oldProperty, _⟩ := stage.preparation.represents.oneGrowingPerSide owner side
  dsimp only at oldProperty
  let oldBlock := stage.preparation.final.blocks.get oldId
  have oldFound : stage.preparation.final.blocks[oldId.val]? = some oldBlock := by simp [oldBlock]
  have kept := stage.preservesGrowingBlock oldFound oldProperty.1 (by
    intro pairing member
    rw [oldProperty.2.1]
    exact notWinner pairing member)
  have idsEq := stage.stable.2.2.2.1.blockId_eq kept found oldProperty.1 growing
    (oldProperty.2.1.trans ownerEq.symm) (oldProperty.2.2.trans sideEq.symm)
  have keptAtId : stage.final.blocks[id.val]? = some oldBlock := by simpa only [idsEq] using kept
  have blockEq : block = oldBlock := Option.some.inj (found.symm.trans keptAtId)
  have wasEmpty := empty oldId
  dsimp only at wasEmpty
  change block.elements = []
  rw [blockEq]
  exact wasEmpty oldProperty.1 oldProperty.2.1 oldProperty.2.2

/-- The accessed root cannot be a pairing winner, so both its new growing
slots remain empty after the complete stage. -/
theorem accessedEmpty : ArticleGrowingOwnerEmpty stage.final (valuePos key) := by
  have notWinner : ∀ pairing ∈ stage.matching, pairing.winner ≠ valuePos key := by
    intro pairing member equal
    have parent := (stage.matching_parents member).1
    have rootEq : stage.preparation.final.view.root = valuePos key := by
      rw [stage.preparation.represents.view_eq]
      exact canonicalRoot_eq_of_rank_eq_zero snapshot before stage.rankZero
    rw [equal, ← rootEq, stage.preparation.final.view.root_parent] at parent
    contradiction
  exact ⟨stage.growingEmptyAt _ .left stage.preparation.accessedEmpty.1 notWinner,
    stage.growingEmptyAt _ .right stage.preparation.accessedEmpty.2 notWinner⟩

/-- Neither boundary wins a pair, so all four prepared boundary growing slots
remain empty through all passes, deletes, inserts and value normalizations. -/
theorem boundaryEmpty (side : Side) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    ArticleGrowingOwnerEmpty stage.final boundary := by
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  let boundary := if side = .left then selection.left else selection.right
  have empty : ArticleGrowingOwnerEmpty stage.preparation.final boundary := by
    cases side with
    | left => exact stage.preparation.leftEmpty
    | right => exact stage.preparation.rightEmpty
  exact ⟨stage.growingEmptyAt _ .left empty.1 (fun pairing member => (stage.endpoints_ne_boundary side member).1),
    stage.growingEmptyAt _ .right empty.2 (fun pairing member => (stage.endpoints_ne_boundary side member).1)⟩

/-- Every geometry with the expected source and terminal boundary has its
block preparation conditions supplied by the actual completed pairing stage. -/
theorem transferConditions (side : Side) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    ∀ geometry : SideTransferGeometry stage.final.view (valuePos key) boundary side,
      geometry.EmptyGrowingSlots ∧ geometry.IsolatedBoundary := by
  dsimp only
  intro geometry
  have emptySlots : geometry.EmptyGrowingSlots := by
    intro block member growing ownerEq sideEq
    obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨lt, getEq⟩ := List.getElem?_eq_some_iff.mp found
    let index : Fin stage.final.blocks.length := ⟨id, lt⟩
    have emptyAt : ArticleGrowingEmptyAt stage.final block.owner side := by
      rcases ownerEq with accessed | boundary
      · rw [accessed]
        cases side with
        | left => exact stage.accessedEmpty.1
        | right => exact stage.accessedEmpty.2
      · rw [boundary]
        cases side with
        | left => exact (stage.boundaryEmpty .left).1
        | right => exact (stage.boundaryEmpty .right).2
    have result := emptyAt index
    dsimp only at result
    rw [show stage.final.blocks.get index = block from getEq] at result
    exact result growing rfl sideEq
  obtain ⟨id, block, found, _, singleton⟩ := stage.boundary_singleton side
  have isolated := geometry.isolatedBoundary_of_found stage.stable found singleton
  exact ⟨emptySlots, isolated⟩

/-- The concrete whole-side transfer can now follow the actual pairing stage.
Its singleton and growing-slot premises are discharged by the same trace. -/
theorem exists_sideTransfer (side : Side)
    (ranks :
      let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
      let boundary := if side = .left then selection.left else selection.right
      ∀ element ∈ (canonicalHeapView snapshot before).topDown (valuePos key) side,
        element ≠ boundary → snapshot.rank boundary < snapshot.rank element) :
    let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
    let boundary := if side = .left then selection.left else selection.right
    ∃ geometry : SideTransferGeometry stage.final.view (valuePos key) boundary side,
      Trace params stage.final [.silent] (stage.final.transferSide geometry stage.stable.2.2.1) ∧
        (stage.final.transferSide geometry stage.stable.2.2.1).Stable params := by
  obtain ⟨geometry⟩ := stage.exists_sideTransferGeometry side ranks
  obtain ⟨emptySlots, isolated⟩ := stage.transferConditions side geometry
  exact ⟨geometry, geometry.transferSide_trace stage.stable emptySlots isolated,
    geometry.transferSide_stable stage.stable emptySlots isolated⟩

end ArticlePairingStage
end Splay.Accounting
