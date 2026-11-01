import Splay.Rank.SplayUpdate
import Splay.Tree.SplayExecution

namespace Splay.Rank

open Splay.Lazy

/--
A dependent finite sequence of exact unit-valued tree-rank updates.

The natural-number index is the exact number of updates.  Each step stores
its own pointwise signed shift and an `IsUnitRotationShift` proof, while the
dependent intermediate tree forces adjacent updates to share an endpoint.
-/
inductive ExactTreeRankUpdateExecution :
    ℕ → {lower upper : ℕ} →
      Tree.BST lower upper → Tree.BST lower upper → Prop
  | refl {lower upper : ℕ} {tree : Tree.BST lower upper} :
      ExactTreeRankUpdateExecution 0 tree tree
  | step {length lower upper : ℕ}
      {before middle after : Tree.BST lower upper}
      {shiftAt : ℕ → ℤ}
      (update : ExactTreeRankUpdate before middle shiftAt)
      (unit : IsUnitRotationShift shiftAt)
      (tail : ExactTreeRankUpdateExecution length middle after) :
      ExactTreeRankUpdateExecution length.succ before after

namespace ExactTreeRankUpdateExecution

/-- One exact unit-valued rank update is a one-step execution. -/
theorem singleton {lower upper : ℕ}
    {before after : Tree.BST lower upper}
    {shiftAt : ℕ → ℤ}
    (update : ExactTreeRankUpdate before after shiftAt)
    (unit : IsUnitRotationShift shiftAt) :
    ExactTreeRankUpdateExecution 1 before after :=
  .step update unit .refl

/-- Concatenation adds the exact numbers of unit rank-update steps. -/
theorem append {firstLength secondLength lower upper : ℕ}
    {before middle after : Tree.BST lower upper}
    (firstPart :
      ExactTreeRankUpdateExecution firstLength before middle)
    (secondPart :
      ExactTreeRankUpdateExecution secondLength middle after) :
    ExactTreeRankUpdateExecution
      (firstLength + secondLength) before after := by
  induction firstPart with
  | refl =>
      simpa using secondPart
  | step update unit tail ih =>
      simpa [Nat.succ_add] using
        (ExactTreeRankUpdateExecution.step
          update unit (ih secondPart))

/--
The indexed comparison-tree interval, and hence the number of stored keys, is
preserved by every exact rank-update execution.
-/
theorem size_eq {length lower upper : ℕ}
    {before after : Tree.BST lower upper}
    (_execution : ExactTreeRankUpdateExecution length before after) :
    before.size = after.size := by
  have beforeSize := before.size_add_lower_eq_upper
  have afterSize := after.size_add_lower_eq_upper
  omega

end ExactTreeRankUpdateExecution

end Splay.Rank

namespace Splay.Lazy.HeapView

open Splay.Rank

/--
The rank-only lazy-view fact retained after forgetting the comparison trees:
one common pointwise shift, unit-valued everywhere, relates every external
element's rank.
-/
def UnitRankUpdate {n : ℕ}
    (before after : HeapView n) : Prop :=
  ∃ shiftAt : ℕ → ℤ,
    IsUnitRotationShift shiftAt ∧
      ∀ element : Element n,
        RankShift before after element
          (shiftAt element.val)

end Splay.Lazy.HeapView

namespace Splay.Rank

open Splay.Lazy

namespace ExactTreeRankUpdate

/--
Forget one exact full-tree unit update to `HeapView.RankShift` for every
external element.  Only equality of the two rank projections with their
tree snapshots is needed; no heap-structure or lazy-block alignment
assumption is used.
-/
theorem toHeapViewUnitRankUpdate {n : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    {shiftAt : ℕ → ℤ}
    (update : ExactTreeRankUpdate beforeTree afterTree shiftAt)
    (unit : IsUnitRotationShift shiftAt)
    {beforeView afterView : HeapView n}
    (beforeRanks :
      beforeView.rank = (Snapshot.ofTree beforeTree).rank)
    (afterRanks :
      afterView.rank = (Snapshot.ofTree afterTree).rank) :
    HeapView.UnitRankUpdate beforeView afterView := by
  refine ⟨shiftAt, unit, ?_⟩
  intro element
  exact update.heapViewRankShift
    beforeRanks afterRanks element

end ExactTreeRankUpdate

end Splay.Rank

namespace Splay.Tree.BST.RotationExecution

open Splay.Rank

/--
Every flat ordinary-rotation execution induces a same-length sequence of
exact unit-valued tree-rank updates over exactly the same intermediate trees.
-/
theorem toExactTreeRankUpdateExecution
    {length lower upper : ℕ}
    {before after : BST lower upper}
    (execution : RotationExecution length before after) :
    ExactTreeRankUpdateExecution length before after := by
  induction execution with
  | refl =>
      exact .refl
  | step rotation tail ih =>
      obtain ⟨shiftAt, update, unit⟩ :=
        rotation.existsExactTreeRankUpdate
      exact .step update unit ih

end Splay.Tree.BST.RotationExecution

namespace Splay.Tree.BST.SplayExecution

open Splay.Rank

/--
A complete splay execution has exactly one unit-valued exact tree-rank update
for each ordinary rotation, hence exactly the accessed key's initial depth
many update steps.
-/
theorem toExactTreeRankUpdateExecution
    {key lower upper : ℕ}
    {before after : BST lower upper}
    (execution : SplayExecution key before after) :
    ExactTreeRankUpdateExecution
      (before.depth key) before after :=
  execution.toRotationExecution.toExactTreeRankUpdateExecution

/--
Total structural/rank form: every in-range key admits a root-ending exact
unit-rank-update execution whose length is its initial search depth.
-/
theorem existsExactTreeRankUpdateExecution
    {key lower upper : ℕ} (tree : BST lower upper)
    (insideLower : lower ≤ key) (insideUpper : key < upper) :
    ∃ after : BST lower upper,
      ExactTreeRankUpdateExecution
          (tree.depth key) tree after ∧
        after.HasRoot key := by
  obtain ⟨after, execution⟩ :=
    SplayExecution.exists_splay tree insideLower insideUpper
  exact
    ⟨after, execution.toExactTreeRankUpdateExecution,
      execution.hasRoot_after⟩

end Splay.Tree.BST.SplayExecution
