import Splay.Accounting.ArticleRelocationPreparation
import Splay.Accounting.CanonicalJunctionSegments
import Splay.Lazy.BlockRelocationGeometry
import Splay.Lazy.SelectedHeapView

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

namespace ArticleRelocationPreparation

variable {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
  {selected owners : Finset (Element n)} {allCuts : Finset ℕ} {before after : Snapshot n} {tree : BST 0 n}
  (execution : ArticleRelocationPreparation params initial selected owners allCuts)
  (viewEq : initial.view = canonicalHeapView before tree)
  (exceptions : junctionExceptionsFrom before after tree (Nat.le_refl n) ⊆ selected)
  (cutSubset : relocationCutsFrom before after tree (Nat.le_refl n) ⊆ allCuts)
  (rootEq : (canonicalHeapView after tree).root = (canonicalHeapView before tree).root)
  (otherOrders : ∀ owner ∉ owners, ∀ side,
    (canonicalHeapView after tree).topDown owner side = (canonicalHeapView before tree).topDown owner side)

include viewEq otherOrders in
theorem canonical_growing_prefixes :
    ∀ block ∈ execution.final.blocks, block.mode = .growing →
      ∃ suffix, (canonicalHeapView after tree).topDown block.owner block.side = block.elements ++ suffix := by
  intro block member growing
  by_cases marked : block.owner ∈ owners
  · refine ⟨(canonicalHeapView after tree).topDown block.owner block.side, ?_⟩
    rw [execution.empty block member growing marked]
    simp
  · rw [otherOrders block.owner marked block.side, ← viewEq, ← execution.view_eq]
    obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨lt, getEq⟩ := List.getElem?_eq_some_iff.mp found
    have result := execution.stable.2.2.2.2.1 ⟨id, lt⟩
    dsimp only at result
    rw [show execution.final.blocks.get ⟨id, lt⟩ = block from getEq] at result
    exact result growing

include viewEq exceptions cutSubset otherOrders in
/-- The preparation's actual blocks satisfy the already proved canonical
junction segment theorem; singleton exceptions may also change side. -/
theorem canonical_block_segment {block : Block n} (member : block ∈ execution.final.blocks)
    (nonempty : block.elements ≠ []) (rootOutside : (canonicalHeapView after tree).root ∉ block.elements) :
    ∃ owner side, IsSegment block.elements ((canonicalHeapView after tree).topDown owner side) := by
  classical
  have fullView := execution.view_eq.trans viewEq
  by_cases exceptional : ∃ element ∈ block.elements, element ∈ selected
  · obtain ⟨element, inside, marked⟩ := exceptional
    have singleton := (execution.singletons element marked block member inside).2
    have parented : (canonicalHeapView after tree).parent element ≠ none := by
      intro absent
      have equal := (canonicalHeapView after tree).parent_eq_none element absent
      exact rootOutside (equal ▸ inside)
    cases parentEq : (canonicalHeapView after tree).parent element with
    | none => exact (parented parentEq).elim
    | some owner =>
        let side := (canonicalHeapView after tree).side element
        have attached : element ∈ (canonicalHeapView after tree).topDown owner side :=
          (canonicalHeapView after tree).mem_topDown_iff.mpr ⟨parentEq, rfl⟩
        obtain ⟨front, back, decomposition⟩ := List.mem_iff_append.mp attached
        refine ⟨owner, side, front, back, ?_⟩
        simpa [singleton] using decomposition
  · have segment := (execution.stable.1.2 block member).isSegment
    rw [execution.stable.2.1.attachedTopDown_eq_topDown, fullView] at segment
    by_cases marked : block.owner ∈ owners
    · obtain ⟨owner, segment⟩ := exists_canonical_segment_after_of_same_relocationCell before after tree nonempty segment
        (fun element inside marked => exceptional ⟨element, inside, exceptions marked⟩)
        (fun first firstIn second secondIn => (execution.cells block member marked first firstIn second secondIn).mono cutSubset)
      exact ⟨owner, block.side, segment⟩
    · exact ⟨block.owner, block.side, by rw [otherOrders block.owner marked block.side]; exact segment⟩

include viewEq exceptions cutSubset rootEq otherOrders in
/-- If the root is unchanged, every nonempty shrinking block satisfies the
root-exclusion premise of the general segment theorem. -/
theorem canonical_shrinking_segments :
    ∀ block ∈ execution.final.blocks, block.mode = .shrinking → block.elements ≠ [] →
      ∃ owner side, IsSegment block.elements ((canonicalHeapView after tree).topDown owner side) := by
  intro block member _shrinking nonempty
  apply execution.canonical_block_segment viewEq exceptions cutSubset otherOrders member nonempty
  intro inside
  have parent := (execution.stable.1.2 block member).parent_eq inside
  rw [execution.view_eq, viewEq, rootEq, (canonicalHeapView before tree).root_parent] at parent
  contradiction

include viewEq exceptions cutSubset rootEq otherOrders in
/-- A concrete relocation geometry for the canonical target structure with
the old numeric ranks, before the two true boundary ranks are restored. -/
theorem canonical_relocationGeometry :
    execution.final.RelocationGeometry ((canonicalHeapView after tree).withRank execution.final.view.rank) := by
  apply State.RelocationGeometry.of_full_segments execution.stable.1 execution.stable.2.1
    ((canonicalHeapView after tree).withRank execution.final.view.rank) rfl
  · change (canonicalHeapView after tree).root = execution.final.view.root
    rw [execution.view_eq, viewEq]
    exact rootEq
  · exact execution.canonical_shrinking_segments viewEq exceptions cutSubset rootEq otherOrders
  · exact execution.canonical_growing_prefixes viewEq otherOrders

end ArticleRelocationPreparation
end Splay.Accounting
