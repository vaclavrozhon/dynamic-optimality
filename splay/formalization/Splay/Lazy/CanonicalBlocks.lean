import Splay.Lazy.CanonicalHeapView

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
All possible placements of a lazy block.  Owners are in symmetric external
node order, and the left placement precedes the right placement for each
owner.
-/
def ownerSidePairs (n : ℕ) : List (Element n × Side) :=
  (List.finRange (2 * n + 1)).product [.left, .right]

@[simp]
theorem mem_ownerSidePairs {n : ℕ} (placement : Element n × Side) :
    placement ∈ ownerSidePairs n := by
  rcases placement with ⟨owner, side⟩
  cases side <;> simp [ownerSidePairs]

/-- Every owner-side placement occurs exactly once. -/
theorem ownerSidePairs_nodup (n : ℕ) :
    (ownerSidePairs n).Nodup := by
  exact
    (List.nodup_finRange (2 * n + 1)).product
      (by simp : ([Side.left, Side.right] : List Side).Nodup)

/-- Exactly the left and right placements have any fixed owner. -/
theorem ownerSidePairs_filter_owner_length {n : ℕ} (owner : Element n) :
    ((ownerSidePairs n).filter fun placement =>
      decide (placement.1 = owner)).length = 2 := by
  have filteredNodup :
      ((ownerSidePairs n).filter fun placement =>
        decide (placement.1 = owner)).Nodup :=
    (ownerSidePairs_nodup n).filter _
  rw [← List.toFinset_card_of_nodup filteredNodup]
  rw [List.toFinset_filter]
  have filteredPairs :
      (ownerSidePairs n).toFinset.filter
          (fun placement => decide (placement.1 = owner) = true) =
        {(owner, .left), (owner, .right)} := by
    ext placement
    rcases placement with ⟨other, side⟩
    cases side <;> simp
  rw [filteredPairs]
  simp

/--
The canonical growing block at one owner-side placement.  It contains the
entire top-down child list at that placement.
-/
noncomputable def canonicalBlock {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) : Block n where
  creator := owner
  owner := owner
  side := side
  passCount := 0
  mode := .growing
  elements := (canonicalHeapView snapshot tree).topDown owner side
  intervalGap := 0

@[simp]
theorem canonicalBlock_creator {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).creator = owner :=
  rfl

@[simp]
theorem canonicalBlock_owner {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).owner = owner :=
  rfl

@[simp]
theorem canonicalBlock_side {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).side = side :=
  rfl

@[simp]
theorem canonicalBlock_passCount {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).passCount = 0 :=
  rfl

@[simp]
theorem canonicalBlock_mode {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).mode = .growing :=
  rfl

@[simp]
theorem canonicalBlock_elements {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).elements =
      (canonicalHeapView snapshot tree).topDown owner side :=
  rfl

@[simp]
theorem canonicalBlock_intervalGap {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).intervalGap = 0 :=
  rfl

/-- The interface projection retains precisely the canonical block payload. -/
@[simp]
theorem canonicalBlock_toInterface {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).toInterface =
      { creator := owner
        passCount := 0
        mode := .growing
        elements := (canonicalHeapView snapshot tree).topDown owner side } :=
  rfl

/-- One canonical block for every owner-side placement. -/
noncomputable def canonicalBlocks {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : List (Block n) :=
  (ownerSidePairs n).map fun placement =>
    canonicalBlock snapshot tree placement.1 placement.2

private theorem canonicalBlock_pair_injective {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    Function.Injective
      (fun placement : Element n × Side =>
        canonicalBlock snapshot tree placement.1 placement.2) := by
  intro first second blocksEq
  apply Prod.ext
  · exact congrArg (fun block : Block n => block.owner) blocksEq
  · exact congrArg (fun block : Block n => block.side) blocksEq

/-- Distinct placements produce distinct canonical blocks. -/
theorem canonicalBlocks_nodup {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (canonicalBlocks snapshot tree).Nodup := by
  exact
    (ownerSidePairs_nodup n).map
      (canonicalBlock_pair_injective snapshot tree)

/-- Exact extensional description of membership in the canonical block list. -/
@[simp]
theorem mem_canonicalBlocks_iff {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) (block : Block n) :
    block ∈ canonicalBlocks snapshot tree ↔
      ∃ owner side, block = canonicalBlock snapshot tree owner side := by
  constructor
  · intro member
    obtain ⟨placement, _, rfl⟩ := List.mem_map.mp member
    exact ⟨placement.1, placement.2, rfl⟩
  · rintro ⟨owner, side, rfl⟩
    exact
      List.mem_map.mpr
        ⟨(owner, side), mem_ownerSidePairs (owner, side), rfl⟩

@[simp]
theorem canonicalBlock_mem_canonicalBlocks {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (owner : Element n) (side : Side) :
    canonicalBlock snapshot tree owner side ∈
      canonicalBlocks snapshot tree := by
  exact (mem_canonicalBlocks_iff snapshot tree _).2
    ⟨owner, side, rfl⟩

/-- Every listed block has all the defining canonical projections. -/
theorem canonicalBlock_spec_of_mem {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) {block : Block n}
    (member : block ∈ canonicalBlocks snapshot tree) :
    block.creator = block.owner ∧
      block.passCount = 0 ∧
      block.mode = .growing ∧
      block.elements =
        (canonicalHeapView snapshot tree).topDown block.owner block.side ∧
      block.intervalGap = 0 := by
  obtain ⟨owner, side, rfl⟩ :=
    (mem_canonicalBlocks_iff snapshot tree block).1 member
  simp

/-- There is exactly one listed block at each owner-side placement. -/
theorem existsUnique_canonicalBlock_at {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (owner : Element n) (side : Side) :
    ∃! block : Block n,
      block ∈ canonicalBlocks snapshot tree ∧
        block.owner = owner ∧ block.side = side := by
  refine
    ⟨canonicalBlock snapshot tree owner side,
      ⟨canonicalBlock_mem_canonicalBlocks snapshot tree owner side,
        rfl, rfl⟩, ?_⟩
  intro block blockSpec
  obtain ⟨otherOwner, otherSide, blockEq⟩ :=
    (mem_canonicalBlocks_iff snapshot tree block).1 blockSpec.1
  rw [blockEq] at blockSpec ⊢
  have ownerEq : otherOwner = owner := blockSpec.2.1
  have sideEq : otherSide = side := blockSpec.2.2
  subst otherOwner
  subst otherSide
  rfl

/--
Index-level form of `existsUnique_canonicalBlock_at`, matching the stable-state
invariant exactly.
-/
theorem existsUnique_canonicalBlock_index_at {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (owner : Element n) (side : Side) :
    ∃! id : Fin (canonicalBlocks snapshot tree).length,
      let block := (canonicalBlocks snapshot tree).get id
      block.mode = .growing ∧
        block.owner = owner ∧ block.side = side := by
  obtain ⟨id, idEq⟩ :=
    List.mem_iff_get.mp
      (canonicalBlock_mem_canonicalBlocks snapshot tree owner side)
  refine ⟨id, ?_, ?_⟩
  · constructor
    · simpa using
        congrArg (fun block : Block n => block.mode) idEq
    · constructor
      · simpa using
          congrArg (fun block : Block n => block.owner) idEq
      · simpa using
          congrArg (fun block : Block n => block.side) idEq
  · intro other otherSpec
    dsimp at otherSpec
    apply (canonicalBlocks_nodup snapshot tree).get_inj_iff.mp
    have otherEq :
        (canonicalBlocks snapshot tree).get other =
          canonicalBlock snapshot tree owner side := by
      exact
        (existsUnique_canonicalBlock_at snapshot tree owner side).unique
          ⟨List.get_mem _ other, otherSpec.2.1, otherSpec.2.2⟩
          ⟨canonicalBlock_mem_canonicalBlocks snapshot tree owner side,
            rfl, rfl⟩
    exact otherEq.trans idEq.symm

/-- Concatenation of the element payloads of all canonical blocks. -/
noncomputable def canonicalAllElements {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : List (Element n) :=
  (canonicalBlocks snapshot tree).flatMap fun block => block.elements

/-- The block concatenation is exactly the concatenation over placements. -/
theorem canonicalAllElements_eq_flatMap_topDown {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    canonicalAllElements snapshot tree =
      (ownerSidePairs n).flatMap fun placement =>
        (canonicalHeapView snapshot tree).topDown
          placement.1 placement.2 := by
  rw [canonicalAllElements, canonicalBlocks, List.flatMap_map]
  rfl

private theorem flatMap_topDown_nodup {n : ℕ} (view : HeapView n) :
    ((ownerSidePairs n).flatMap fun placement =>
      view.topDown placement.1 placement.2).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro placement _
    exact view.topDown_nodup placement.1 placement.2
  · apply (ownerSidePairs_nodup n).imp
    intro first second distinct
    change
      List.Disjoint
        (view.topDown first.1 first.2)
        (view.topDown second.1 second.2)
    rw [List.disjoint_left]
    intro element firstMember secondMember
    apply distinct
    apply Prod.ext
    · have firstParent :=
        (view.mem_topDown_iff.mp firstMember).1
      have secondParent :=
        (view.mem_topDown_iff.mp secondMember).1
      exact Option.some.inj (firstParent.symm.trans secondParent)
    · have firstSide :=
        (view.mem_topDown_iff.mp firstMember).2
      have secondSide :=
        (view.mem_topDown_iff.mp secondMember).2
      exact firstSide.symm.trans secondSide

/-- No vertex occurs in two canonical blocks. -/
theorem canonicalAllElements_nodup {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (canonicalAllElements snapshot tree).Nodup := by
  rw [canonicalAllElements_eq_flatMap_topDown]
  exact flatMap_topDown_nodup (canonicalHeapView snapshot tree)

/-- The concatenation covers exactly the vertices having a heap parent. -/
theorem mem_canonicalAllElements_iff_parent_ne_none {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    element ∈ canonicalAllElements snapshot tree ↔
      (canonicalHeapView snapshot tree).parent element ≠ none := by
  rw [canonicalAllElements_eq_flatMap_topDown]
  constructor
  · intro member
    obtain ⟨placement, _, elementMember⟩ :=
      List.mem_flatMap.mp member
    have parent :=
      ((canonicalHeapView snapshot tree).mem_topDown_iff.mp
        elementMember).1
    rw [parent]
    simp
  · intro parentNe
    cases parentEq :
        (canonicalHeapView snapshot tree).parent element with
    | none =>
        exact (parentNe parentEq).elim
    | some owner =>
        apply List.mem_flatMap.mpr
        refine
          ⟨(owner, (canonicalHeapView snapshot tree).side element),
            mem_ownerSidePairs _, ?_⟩
        exact
          (canonicalHeapView snapshot tree).mem_topDown_iff.mpr
            ⟨parentEq, rfl⟩

/-- Equivalently, the concatenation contains exactly every non-root vertex. -/
theorem mem_canonicalAllElements_iff_ne_root {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (element : Element n) :
    element ∈ canonicalAllElements snapshot tree ↔
      element ≠ canonicalRoot snapshot tree := by
  rw [mem_canonicalAllElements_iff_parent_ne_none]
  constructor
  · intro parentNe elementEq
    subst element
    exact parentNe
      (canonicalHeapView snapshot tree).root_parent
  · intro notRoot
    exact
      (canonicalHeapView snapshot tree).parent_ne_none_of_ne_root
        notRoot

/--
The interface projection has exactly the two canonical growing blocks created
by each owner.
-/
theorem canonicalBlocks_growingCount {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (value : Element n → ℕ) (creator : Element n) :
    let state : Interface.State n :=
      { blocks := (canonicalBlocks snapshot tree).map Block.toInterface
        value := value }
    state.growingCount creator = 2 := by
  simp only [Interface.State.growingCount]
  rw [List.filter_map, List.length_map]
  rw [canonicalBlocks, List.filter_map, List.length_map]
  have predicateEq :
      (((fun block : Interface.Block n =>
          decide
            (block.mode = .growing ∧ block.creator = creator)) ∘
          Block.toInterface) ∘
        fun placement : Element n × Side =>
          canonicalBlock snapshot tree placement.1 placement.2) =
        (fun placement : Element n × Side =>
          decide (placement.1 = creator)) := by
    funext placement
    simp [Function.comp_def]
  rw [predicateEq]
  exact ownerSidePairs_filter_owner_length creator

end Splay.Lazy.Canonical
