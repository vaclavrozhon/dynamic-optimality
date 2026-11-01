import Splay.Lazy.CanonicalBlocks
import Splay.Lazy.CanonicalValues

namespace Splay.Lazy.Canonical

open Splay.Rank

/--
The stable lazy state canonically induced by a rank snapshot and a comparison
tree.
-/
noncomputable def canonicalState {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) : State n where
  view := canonicalHeapView snapshot tree
  blocks := canonicalBlocks snapshot tree
  value := canonicalValue snapshot tree

@[simp]
theorem canonicalState_view {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).view =
      canonicalHeapView snapshot tree :=
  rfl

@[simp]
theorem canonicalState_blocks {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).blocks =
      canonicalBlocks snapshot tree :=
  rfl

@[simp]
theorem canonicalState_value {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).value =
      canonicalValue snapshot tree :=
  rfl

@[simp]
theorem canonicalState_allElements {n : ℕ} (snapshot : Snapshot n)
    (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).allElements =
      canonicalAllElements snapshot tree :=
  rfl

/--
Because the canonical blocks cover every non-root vertex, restricting a
canonical top-down list to assigned vertices removes nothing.
-/
theorem canonical_attachedTopDown_eq_topDown {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (owner : Element n) (side : Side) :
    (canonicalHeapView snapshot tree).attachedTopDown
        (canonicalAllElements snapshot tree) owner side =
      (canonicalHeapView snapshot tree).topDown owner side := by
  unfold HeapView.attachedTopDown
  apply List.filter_eq_self.mpr
  intro element member
  simp only [decide_eq_true_eq]
  apply
    (mem_canonicalAllElements_iff_parent_ne_none
      snapshot tree element).2
  have parent :=
    ((canonicalHeapView snapshot tree).mem_topDown_iff.mp member).1
  rw [parent]
  simp

/-- Every canonical block satisfies the complete local transient invariant. -/
theorem canonicalBlock_structurallyValid {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (owner : Element n) (side : Side) :
    (canonicalBlock snapshot tree owner side).StructurallyValid
      (canonicalHeapView snapshot tree)
      (canonicalAllElements snapshot tree) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [canonical_attachedTopDown_eq_topDown]
    exact ⟨[], [], by simp⟩
  · intro _
    rfl
  · simp only [Block.GapValid, canonicalBlock_mode]
    constructor
    · rfl
    · intro element member
      have parent :=
        ((canonicalHeapView snapshot tree).mem_topDown_iff.mp
          member).1
      exact
        le_of_lt
          ((canonicalHeapView snapshot tree).rawGap_pos_of_heapOrdered
            (canonicalHeapView_heapOrdered snapshot tree) parent)

/-- Every listed canonical block is structurally valid. -/
theorem canonicalBlock_structurallyValid_of_mem {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    {block : Block n} (member : block ∈ canonicalBlocks snapshot tree) :
    block.StructurallyValid
      (canonicalHeapView snapshot tree)
      (canonicalAllElements snapshot tree) := by
  obtain ⟨owner, side, rfl⟩ :=
    (mem_canonicalBlocks_iff snapshot tree block).1 member
  exact canonicalBlock_structurallyValid snapshot tree owner side

/--
The abstract projection of the canonical state is valid whenever the interface
allows its two growing blocks per creator and the contracted maximum rank fits
inside the value bound.
-/
theorem canonicalState_toInterface_valid {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (canonicalState snapshot tree).toInterface.Valid params := by
  refine ⟨?_, ?_, ?_⟩
  · rw [State.toInterface_allElements, canonicalState_allElements]
    exact canonicalAllElements_nodup snapshot tree
  · intro element
    constructor
    · exact canonicalValue_pos snapshot tree element
    · exact
        (canonicalValue_le_contractedGap_maxRank
          snapshot tree element).trans valueBound
  · intro creator
    have countEq :=
      canonicalBlocks_growingCount
        snapshot tree (canonicalValue snapshot tree) creator
    change
      (canonicalState snapshot tree).toInterface.growingCount creator ≤
        params.growingLimit
    have projectedCount :
        (canonicalState snapshot tree).toInterface.growingCount creator =
          2 := by
      simpa [canonicalState, State.toInterface] using countEq
    rw [projectedCount]
    exact growingLimit

/-- The canonical rich state satisfies transient validity. -/
theorem canonicalState_valid {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (canonicalState snapshot tree).Valid params := by
  refine
    ⟨canonicalState_toInterface_valid
      snapshot tree params growingLimit valueBound, ?_⟩
  intro block member
  exact canonicalBlock_structurallyValid_of_mem snapshot tree member

/-- Canonical blocks contain exactly every vertex with a heap parent. -/
theorem canonicalState_complete {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).Complete := by
  intro element
  exact mem_canonicalAllElements_iff_parent_ne_none snapshot tree element

/-- The canonical state has exactly one growing block at each placement. -/
theorem canonicalState_oneGrowingPerSide {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).OneGrowingPerSide := by
  intro owner side
  exact existsUnique_canonicalBlock_index_at snapshot tree owner side

/-- Every canonical growing block is the whole top-down list at its placement. -/
theorem canonicalState_growingTopmost {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).GrowingTopmost := by
  intro id
  dsimp
  intro _
  have member :
      (canonicalBlocks snapshot tree)[id.val] ∈
        canonicalBlocks snapshot tree :=
    List.getElem_mem (by exact id.isLt)
  have spec := canonicalBlock_spec_of_mem snapshot tree member
  refine ⟨[], ?_⟩
  simpa only [List.append_nil] using spec.2.2.2.1.symm

/-- Canonical values realize the zero-interval-gap value of every block. -/
theorem canonicalState_valuesRealizeGaps {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    (canonicalState snapshot tree).ValuesRealizeGaps := by
  constructor
  · exact canonicalValue_canonicalRoot snapshot tree
  · intro block member element _
    have spec := canonicalBlock_spec_of_mem snapshot tree member
    rw [spec.2.2.2.2]
    rfl

/--
The canonical state is a stable lazy state under exactly the two numerical
conditions needed by the abstract interface.
-/
theorem canonicalState_stable {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    (canonicalState snapshot tree).Stable params := by
  refine
    ⟨canonicalState_valid
        snapshot tree params growingLimit valueBound,
      canonicalState_complete snapshot tree,
      canonicalHeapView_heapOrdered snapshot tree,
      canonicalState_oneGrowingPerSide snapshot tree,
      canonicalState_growingTopmost snapshot tree,
      canonicalState_valuesRealizeGaps snapshot tree⟩

end Splay.Lazy.Canonical
