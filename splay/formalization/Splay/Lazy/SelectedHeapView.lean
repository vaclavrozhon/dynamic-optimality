import Splay.Lazy.CanonicalHeapView
import Splay.Lazy.RankUpdate

namespace Splay.Lazy

namespace HeapView

/--
Replace only the numeric ranks of a transient heap view.

The structural parent relation, side orders, top-down lists, and acyclicity
levels remain those selected by the original view.  This is the basic
separation needed for the manuscript's order-only temporary priorities:
selection may change while signed gaps continue to use true numeric ranks.
-/
def withRank {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) : HeapView n where
  rank := numericRank
  root := view.root
  parent := view.parent
  side := view.side
  topDown := view.topDown
  level := view.level
  root_parent := view.root_parent
  parent_eq_none := view.parent_eq_none
  parent_level_lt := view.parent_level_lt
  side_order := view.side_order
  topDown_nodup := view.topDown_nodup
  topDown_ordered := view.topDown_ordered
  mem_topDown_iff := view.mem_topDown_iff

@[simp]
theorem withRank_rank {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) :
    (view.withRank numericRank).rank = numericRank :=
  rfl

@[simp]
theorem withRank_root {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) :
    (view.withRank numericRank).root = view.root :=
  rfl

@[simp]
theorem withRank_parent {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) :
    (view.withRank numericRank).parent = view.parent :=
  rfl

@[simp]
theorem withRank_side {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) :
    (view.withRank numericRank).side = view.side :=
  rfl

@[simp]
theorem withRank_topDown {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) :
    (view.withRank numericRank).topDown = view.topDown :=
  rfl

/-- Rank replacement is structurally invisible. -/
theorem sameStructure_withRank {n : ℕ} (view : HeapView n)
    (numericRank : Element n → ℕ) :
    view.SameStructure (view.withRank numericRank) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Replacing ranks twice retains only the last numeric rank function. -/
@[simp]
theorem withRank_withRank {n : ℕ} (view : HeapView n)
    (first second : Element n → ℕ) :
    (view.withRank first).withRank second = view.withRank second :=
  rfl

end HeapView

namespace Canonical

open Splay.Rank

/--
Use one snapshot to select the canonical heavy-path structure while carrying
an independent true numeric rank in raw-gap calculations.
-/
noncomputable def canonicalHeapViewWithRank {n : ℕ}
    (selection : Snapshot n) (numericRank : Element n → ℕ)
    (tree : Tree.BST 0 n) : HeapView n :=
  (canonicalHeapView selection tree).withRank numericRank

@[simp]
theorem canonicalHeapViewWithRank_rank {n : ℕ}
    (selection : Snapshot n) (numericRank : Element n → ℕ)
    (tree : Tree.BST 0 n) :
    (canonicalHeapViewWithRank selection numericRank tree).rank =
      numericRank :=
  rfl

@[simp]
theorem canonicalHeapViewWithRank_parent {n : ℕ}
    (selection : Snapshot n) (numericRank : Element n → ℕ)
    (tree : Tree.BST 0 n) :
    (canonicalHeapViewWithRank selection numericRank tree).parent =
      canonicalParent selection tree :=
  rfl

@[simp]
theorem canonicalHeapViewWithRank_trueRank {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n) :
    canonicalHeapViewWithRank snapshot snapshot.rank tree =
      canonicalHeapView snapshot tree := by
  rfl

/--
The selected structure is heap-ordered by an independent numeric rank exactly
when every selected parent edge respects that numeric rank.
-/
theorem canonicalHeapViewWithRank_heapOrdered_iff {n : ℕ}
    (selection : Snapshot n) (numericRank : Element n → ℕ)
    (tree : Tree.BST 0 n) :
    (canonicalHeapViewWithRank selection numericRank tree).HeapOrdered ↔
      ∀ {child owner},
        canonicalParent selection tree child = some owner →
          numericRank owner < numericRank child := by
  rfl

end Canonical

end Splay.Lazy
