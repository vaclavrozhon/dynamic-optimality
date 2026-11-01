import Splay.Lazy.RankUpdate
import Splay.Rank.FromTree
import Splay.Tree.RotationDepthBound

namespace Splay.Rank.Snapshot

open Splay.Lazy

/--
Two transient heap views carry the comparison ranks immediately before and
after one (possibly contextual) comparison-tree rotation.
-/
structure RotationRanks {n depth : ℕ}
    (beforeTree afterTree : Tree.BST 0 n)
    (beforeView afterView : HeapView n) : Prop where
  rotates : Tree.BST.RotationAt depth beforeTree afterTree
  before_eq : beforeView.rank = (ofTree beforeTree).rank
  after_eq : afterView.rank = (ofTree afterTree).rank

namespace RotationRanks

/--
Every external-node rank changes by at most one under one contextual
comparison-tree rotation.
-/
theorem rank_within_one {n depth : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    {beforeView afterView : HeapView n}
    (ranks :
      RotationRanks (depth := depth)
        beforeTree afterTree beforeView afterView)
    (element : Element n) :
    afterView.rank element ≤ beforeView.rank element + 1 ∧
      beforeView.rank element ≤ afterView.rank element + 1 := by
  rw [ranks.before_eq, ranks.after_eq]
  exact ranks.rotates.externalDepth_within_one element.val

/--
Pointwise, a contextual rotation has one of the three exact signed rank
shifts `-1`, `0`, or `1`.
-/
theorem exists_rankShift {n depth : ℕ}
    {beforeTree afterTree : Tree.BST 0 n}
    {beforeView afterView : HeapView n}
    (ranks :
      RotationRanks (depth := depth)
        beforeTree afterTree beforeView afterView)
    (element : Element n) :
    ∃ shift : ℤ,
      (shift = -1 ∨ shift = 0 ∨ shift = 1) ∧
        HeapView.RankShift beforeView afterView element shift := by
  obtain ⟨shift, hShift, hDepth⟩ :=
    ranks.rotates.exists_signedShift element.val
  refine ⟨shift, hShift, ?_⟩
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  exact hDepth

end RotationRanks

end Splay.Rank.Snapshot
