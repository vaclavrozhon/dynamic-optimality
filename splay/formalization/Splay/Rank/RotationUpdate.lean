import Splay.Lazy.RankUpdate
import Splay.Rank.FromTree
import Splay.Tree.RotationDepth

namespace Splay.Rank.Snapshot

open Splay.Lazy

/--
The ranks carried by two transient heap views are exactly the ranks of the
comparison trees on the two sides of a right root rotation.

Keeping this relation separate from `HeapView.SameStructure` reflects the
non-atomic update: the heap structure may already have been installed before
the comparison-tree ranks are changed.
-/
structure RightRotationRanks {n promoted demoted : ℕ}
    (a : Tree.BST 0 promoted)
    (b : Tree.BST (promoted + 1) demoted)
    (c : Tree.BST (demoted + 1) n)
    (before after : HeapView n) : Prop where
  before_eq :
    before.rank =
      (ofTree (.node (.node a b) c)).rank
  after_eq :
    after.rank =
      (ofTree (.node a (.node b c))).rank

namespace RightRotationRanks

/--
The complete signed rank update of a right rotation, as a function of the
external inorder position.
-/
def shiftAt (promoted demoted position : ℕ) : ℤ :=
  if position ≤ 2 * promoted + 1 then -1
  else if position < 2 * demoted + 1 then 0
  else 1

/--
In the promoted (leftmost) sector of a right rotation, every rank decreases
by exactly one.
-/
theorem promotedSector {n promoted demoted : ℕ}
    {a : Tree.BST 0 promoted}
    {b : Tree.BST (promoted + 1) demoted}
    {c : Tree.BST (demoted + 1) n}
    {before after : HeapView n}
    (ranks : RightRotationRanks a b c before after)
    (element : Element n)
    (position : element.val ≤ 2 * promoted + 1) :
    HeapView.RankShift before after element (-1 : ℤ) := by
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  change
    (Tree.BST.externalDepth (.node a (.node b c)) element.val : ℤ) =
      (Tree.BST.externalDepth (.node (.node a b) c) element.val : ℤ) - 1
  have depth :=
    Tree.BST.RootRotation.right_externalDepth_promotedSector
      a b c position
  omega

/--
In the middle sector of a right rotation, every rank is unchanged.
-/
theorem middleSector {n promoted demoted : ℕ}
    {a : Tree.BST 0 promoted}
    {b : Tree.BST (promoted + 1) demoted}
    {c : Tree.BST (demoted + 1) n}
    {before after : HeapView n}
    (ranks : RightRotationRanks a b c before after)
    (element : Element n)
    (abovePromoted : 2 * promoted + 1 < element.val)
    (belowDemoted : element.val < 2 * demoted + 1) :
    HeapView.RankShift before after element 0 := by
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  change
    (Tree.BST.externalDepth (.node a (.node b c)) element.val : ℤ) =
      (Tree.BST.externalDepth (.node (.node a b) c) element.val : ℤ) + 0
  have depth :=
    Tree.BST.RootRotation.right_externalDepth_middleSector
      a b c abovePromoted belowDemoted
  omega

/--
In the demoted (rightmost) sector of a right rotation, every rank increases
by exactly one.
-/
theorem demotedSector {n promoted demoted : ℕ}
    {a : Tree.BST 0 promoted}
    {b : Tree.BST (promoted + 1) demoted}
    {c : Tree.BST (demoted + 1) n}
    {before after : HeapView n}
    (ranks : RightRotationRanks a b c before after)
    (element : Element n)
    (position : 2 * demoted + 1 ≤ element.val) :
    HeapView.RankShift before after element (1 : ℤ) := by
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  change
    (Tree.BST.externalDepth (.node a (.node b c)) element.val : ℤ) =
      (Tree.BST.externalDepth (.node (.node a b) c) element.val : ℤ) + 1
  have depth :=
    Tree.BST.RootRotation.right_externalDepth_demotedSector
      a b c position
  omega

/--
Every external position receives exactly the right-rotation shift selected by
`shiftAt`; the three preceding sector lemmas are its convenient projections.
-/
theorem rankShift {n promoted demoted : ℕ}
    {a : Tree.BST 0 promoted}
    {b : Tree.BST (promoted + 1) demoted}
    {c : Tree.BST (demoted + 1) n}
    {before after : HeapView n}
    (ranks : RightRotationRanks a b c before after)
    (element : Element n) :
    HeapView.RankShift before after element
      (shiftAt promoted demoted element.val) := by
  unfold shiftAt
  split
  · next position =>
      exact ranks.promotedSector element position
  · next notPromoted =>
      split
      · next belowDemoted =>
          exact ranks.middleSector element (by omega) belowDemoted
      · next notBelowDemoted =>
          exact ranks.demotedSector element (by omega)

end RightRotationRanks

/--
The ranks carried by two transient heap views are exactly the ranks of the
comparison trees on the two sides of a left root rotation.
-/
structure LeftRotationRanks {n demoted promoted : ℕ}
    (a : Tree.BST 0 demoted)
    (b : Tree.BST (demoted + 1) promoted)
    (c : Tree.BST (promoted + 1) n)
    (before after : HeapView n) : Prop where
  before_eq :
    before.rank =
      (ofTree (.node a (.node b c))).rank
  after_eq :
    after.rank =
      (ofTree (.node (.node a b) c)).rank

namespace LeftRotationRanks

/--
The complete signed rank update of a left rotation, as a function of the
external inorder position.
-/
def shiftAt (demoted promoted position : ℕ) : ℤ :=
  if position ≤ 2 * demoted + 1 then 1
  else if position < 2 * promoted + 1 then 0
  else -1

/--
In the demoted (leftmost) sector of a left rotation, every rank increases by
exactly one.
-/
theorem demotedSector {n demoted promoted : ℕ}
    {a : Tree.BST 0 demoted}
    {b : Tree.BST (demoted + 1) promoted}
    {c : Tree.BST (promoted + 1) n}
    {before after : HeapView n}
    (ranks : LeftRotationRanks a b c before after)
    (element : Element n)
    (position : element.val ≤ 2 * demoted + 1) :
    HeapView.RankShift before after element (1 : ℤ) := by
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  change
    (Tree.BST.externalDepth (.node (.node a b) c) element.val : ℤ) =
      (Tree.BST.externalDepth (.node a (.node b c)) element.val : ℤ) + 1
  have depth :=
    Tree.BST.RootRotation.left_externalDepth_demotedSector
      a b c position
  omega

/--
In the middle sector of a left rotation, every rank is unchanged.
-/
theorem middleSector {n demoted promoted : ℕ}
    {a : Tree.BST 0 demoted}
    {b : Tree.BST (demoted + 1) promoted}
    {c : Tree.BST (promoted + 1) n}
    {before after : HeapView n}
    (ranks : LeftRotationRanks a b c before after)
    (element : Element n)
    (aboveDemoted : 2 * demoted + 1 < element.val)
    (belowPromoted : element.val < 2 * promoted + 1) :
    HeapView.RankShift before after element 0 := by
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  change
    (Tree.BST.externalDepth (.node (.node a b) c) element.val : ℤ) =
      (Tree.BST.externalDepth (.node a (.node b c)) element.val : ℤ) + 0
  have depth :=
    Tree.BST.RootRotation.left_externalDepth_middleSector
      a b c aboveDemoted belowPromoted
  omega

/--
In the promoted (rightmost) sector of a left rotation, every rank decreases by
exactly one.
-/
theorem promotedSector {n demoted promoted : ℕ}
    {a : Tree.BST 0 demoted}
    {b : Tree.BST (demoted + 1) promoted}
    {c : Tree.BST (promoted + 1) n}
    {before after : HeapView n}
    (ranks : LeftRotationRanks a b c before after)
    (element : Element n)
    (position : 2 * promoted + 1 ≤ element.val) :
    HeapView.RankShift before after element (-1 : ℤ) := by
  unfold HeapView.RankShift
  rw [ranks.before_eq, ranks.after_eq]
  change
    (Tree.BST.externalDepth (.node (.node a b) c) element.val : ℤ) =
      (Tree.BST.externalDepth (.node a (.node b c)) element.val : ℤ) - 1
  have depth :=
    Tree.BST.RootRotation.left_externalDepth_promotedSector
      a b c position
  omega

/--
Every external position receives exactly the left-rotation shift selected by
`shiftAt`; the three preceding sector lemmas are its convenient projections.
-/
theorem rankShift {n demoted promoted : ℕ}
    {a : Tree.BST 0 demoted}
    {b : Tree.BST (demoted + 1) promoted}
    {c : Tree.BST (promoted + 1) n}
    {before after : HeapView n}
    (ranks : LeftRotationRanks a b c before after)
    (element : Element n) :
    HeapView.RankShift before after element
      (shiftAt demoted promoted element.val) := by
  unfold shiftAt
  split
  · next position =>
      exact ranks.demotedSector element position
  · next notDemoted =>
      split
      · next belowPromoted =>
          exact ranks.middleSector element (by omega) belowPromoted
      · next notBelowPromoted =>
          exact ranks.promotedSector element (by omega)

end LeftRotationRanks

end Splay.Rank.Snapshot
