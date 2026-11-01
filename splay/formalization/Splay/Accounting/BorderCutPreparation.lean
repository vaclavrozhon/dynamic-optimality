import Splay.Accounting.CanonicalBorderOwners
import Splay.Accounting.ArticleRelocationPreparation

namespace Splay.Accounting

open Splay.Rank Splay.Tree Splay.Lazy Splay.Lazy.Canonical JunctionBendReduction

/-- Owners of intervals crossing any selected numerical rank-update border.
The witness may be either adjacent endpoint of its cut. -/
noncomputable def borderCutOwners {n : ℕ} (snapshot : Snapshot n) (cuts : Finset ℕ)
    (border : ℕ → External n) : Finset (External n) :=
  cuts.biUnion fun cut => snapshot.coveringMinima (border cut)

theorem borderCutOwners_card_le {n : ℕ} (snapshot : Snapshot n) (cuts : Finset ℕ)
    (border : ℕ → External n) (rankBound : ℕ) (bounded : ∀ cut ∈ cuts, snapshot.rank (border cut) ≤ rankBound) :
    (borderCutOwners snapshot cuts border).card ≤ cuts.card * (rankBound + 1) := by
  classical
  have unionBound := Finset.card_biUnion_le (s := cuts) (t := fun cut => snapshot.coveringMinima (border cut))
  have sumBound : (∑ cut ∈ cuts, (snapshot.coveringMinima (border cut)).card) ≤ ∑ _cut ∈ cuts, (rankBound + 1) := by
    apply Finset.sum_le_sum
    intro cut member
    exact (snapshot.coveringMinima_card_le (border cut)).trans (Nat.add_le_add_right (bounded cut member) 1)
  change (cuts.biUnion fun cut => snapshot.coveringMinima (border cut)).card ≤ _
  simpa using unionBound.trans sumBound

theorem borderCutOwners_no_crossing {n : ℕ} {params : Interface.Parameters} {state : Lazy.State n}
    (valid : state.Valid params) (snapshot : Snapshot n) (tree : BST 0 n)
    (viewEq : state.view = canonicalHeapView snapshot tree) (cuts : Finset ℕ) (border : ℕ → External n)
    (adjacent : ∀ cut ∈ cuts, (border cut).val = cut ∨ (border cut).val + 1 = cut)
    {block : Block n} (member : block ∈ state.blocks) (outside : block.owner ∉ borderCutOwners snapshot cuts border) :
    ∀ cut ∈ cuts, ¬ block.CrossesCut cut := by
  classical
  intro cut cutIn crossing
  have covers := canonicalBlock_owner_mem_coveringMinima_of_crossesCut valid snapshot tree viewEq member cut (border cut)
    (adjacent cut cutIn) crossing
  exact outside (Finset.mem_biUnion.mpr ⟨cut, cutIn, covers⟩)

/-- Away from the covering-owner support, an owner and every actual child
are in the same cell of all numerical rank-update cuts. -/
theorem borderCutOwners_parent_sameCell {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (cuts : Finset ℕ) (border : ℕ → External n)
    (adjacent : ∀ cut ∈ cuts, (border cut).val = cut ∨ (border cut).val + 1 = cut)
    {owner child : External n} (parent : canonicalParent snapshot tree child = some owner)
    (outside : owner ∉ borderCutOwners snapshot cuts border) : SameCutCell cuts owner child := by
  classical
  intro cut member
  have sameSide : ¬ ((owner.val < cut ∧ cut ≤ child.val) ∨ (child.val < cut ∧ cut ≤ owner.val)) := by
    intro separated
    have between : (owner ≤ border cut ∧ border cut ≤ child) ∨ (child ≤ border cut ∧ border cut ≤ owner) := by
      have borderAdj := adjacent cut member
      simp only [Fin.le_def]
      omega
    have covers := canonicalOwner_mem_coveringMinima_of_between_parent_child snapshot tree parent between
    exact outside (Finset.mem_biUnion.mpr ⟨cut, member, covers⟩)
  omega

namespace ArticleRelocationPreparation

/-- Only marked owners require actual splits. Every unmarked block already
stays in one rank-update cell by the canonical border-owner geometry. -/
theorem all_blocks_sameCell {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {selected owners : Finset (Element n)}
    {allCuts shiftCuts : Finset ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (execution : ArticleRelocationPreparation params initial selected owners allCuts)
    (viewEq : initial.view = canonicalHeapView snapshot tree) (border : ℕ → External n)
    (adjacent : ∀ cut ∈ shiftCuts, (border cut).val = cut ∨ (border cut).val + 1 = cut)
    (ownerSubset : borderCutOwners snapshot shiftCuts border ⊆ owners) (cutSubset : shiftCuts ⊆ allCuts)
    {block : Block n} (member : block ∈ execution.final.blocks) :
    ∀ first ∈ block.elements, ∀ second ∈ block.elements, SameCutCell shiftCuts first second := by
  intro first firstIn second secondIn
  by_cases marked : block.owner ∈ owners
  · exact (execution.cells block member marked first firstIn second secondIn).mono cutSubset
  · have outside : block.owner ∉ borderCutOwners snapshot shiftCuts border := fun inside => marked (ownerSubset inside)
    have clear := borderCutOwners_no_crossing execution.stable.1 snapshot tree (execution.view_eq.trans viewEq)
      shiftCuts border adjacent member outside
    intro cut cutMember
    have notCross := clear cut cutMember
    constructor
    · intro firstLow
      by_contra secondNotLow
      exact notCross ⟨first, firstIn, second, secondIn, firstLow, by omega⟩
    · intro secondLow
      by_contra firstNotLow
      exact notCross ⟨second, secondIn, first, firstIn, secondLow, by omega⟩

/-- Every surviving growing child has exactly its owner's rank-update cell;
all growing intervals at potentially exceptional owners were converted. -/
theorem growing_owner_sameCell {n : ℕ} {params : Interface.Parameters} {initial : Lazy.State n}
    {selected owners : Finset (Element n)} {allCuts shiftCuts : Finset ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n)
    (execution : ArticleRelocationPreparation params initial selected owners allCuts)
    (viewEq : initial.view = canonicalHeapView snapshot tree) (border : ℕ → External n)
    (adjacent : ∀ cut ∈ shiftCuts, (border cut).val = cut ∨ (border cut).val + 1 = cut)
    (ownerSubset : borderCutOwners snapshot shiftCuts border ⊆ owners)
    {block : Block n} (member : block ∈ execution.final.blocks) (growing : block.mode = .growing)
    {element : Element n} (inside : element ∈ block.elements) : SameCutCell shiftCuts block.owner element := by
  have outside : block.owner ∉ owners := by
    intro marked
    rw [execution.empty block member growing marked] at inside
    simp at inside
  have parent := (execution.stable.1.2 block member).parent_eq inside
  rw [execution.view_eq, viewEq] at parent
  exact borderCutOwners_parent_sameCell snapshot tree shiftCuts border adjacent parent
    (fun marked => outside (ownerSubset marked))

end ArticleRelocationPreparation
end Splay.Accounting
