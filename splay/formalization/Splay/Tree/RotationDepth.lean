import Splay.Tree.External
import Splay.Tree.Rotation

namespace Splay.Tree.BST.RootRotation

/--
Under a right root rotation, the depth of every external position in the
promoted sector decreases by one.

The sector includes both all positions of `a` (which end at
`2 * promoted`) and the promoted value itself at `2 * promoted + 1`.
The equality is written with `succ` to avoid truncated subtraction on
natural-number depths.
-/
theorem right_externalDepth_promotedSector
    {lower promoted demoted upper position : ℕ}
    (a : BST lower promoted)
    (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) upper)
    (hPosition : position ≤ 2 * promoted + 1) :
    (externalDepth (.node a (.node b c)) position).succ =
      externalDepth (.node (.node a b) c) position := by
  have hPromotedDemoted : promoted < demoted := by
    have := b.lower_le_upper
    omega
  by_cases hLeft : position < 2 * promoted + 1
  · have hOuterLeft : position < 2 * demoted + 1 := by omega
    rw [externalDepth_node_of_lt_root a (.node b c) hLeft]
    rw [externalDepth_node_of_lt_root (.node a b) c hOuterLeft]
    rw [externalDepth_node_of_lt_root a b hLeft]
  · have hRoot : position = 2 * promoted + 1 := by omega
    subst position
    have hOuterLeft : 2 * promoted + 1 < 2 * demoted + 1 := by omega
    rw [externalDepth_root a (.node b c)]
    rw [externalDepth_node_of_lt_root (.node a b) c hOuterLeft]
    rw [externalDepth_root a b]

/--
Under a right root rotation, depths are unchanged strictly between the
promoted and demoted value positions.

For natural positions, these hypotheses describe exactly the closed interval
`[2 * promoted + 2, 2 * demoted]`, namely all external positions of `b`.
-/
theorem right_externalDepth_middleSector
    {lower promoted demoted upper position : ℕ}
    (a : BST lower promoted)
    (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) upper)
    (hPromoted : 2 * promoted + 1 < position)
    (hDemoted : position < 2 * demoted + 1) :
    externalDepth (.node (.node a b) c) position =
      externalDepth (.node a (.node b c)) position := by
  rw [externalDepth_node_of_lt_root (.node a b) c hDemoted]
  rw [externalDepth_node_of_root_lt a b hPromoted]
  rw [externalDepth_node_of_root_lt a (.node b c) hPromoted]
  rw [externalDepth_node_of_lt_root b c hDemoted]

/--
Under a right root rotation, the depth of every external position in the
demoted sector increases by one.

The sector starts with the demoted value itself at `2 * demoted + 1`; the
remaining positions are those of `c`.
-/
theorem right_externalDepth_demotedSector
    {lower promoted demoted upper position : ℕ}
    (a : BST lower promoted)
    (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) upper)
    (hPosition : 2 * demoted + 1 ≤ position) :
    (externalDepth (.node (.node a b) c) position).succ =
      externalDepth (.node a (.node b c)) position := by
  have hPromotedDemoted : promoted < demoted := by
    have := b.lower_le_upper
    omega
  have hOuterRight : 2 * promoted + 1 < position := by omega
  by_cases hRoot : position = 2 * demoted + 1
  · subst position
    rw [externalDepth_root (.node a b) c]
    rw [externalDepth_node_of_root_lt a (.node b c) (by omega)]
    rw [externalDepth_root b c]
  · have hRight : 2 * demoted + 1 < position := by omega
    rw [externalDepth_node_of_root_lt (.node a b) c hRight]
    rw [externalDepth_node_of_root_lt a (.node b c) hOuterRight]
    rw [externalDepth_node_of_root_lt b c hRight]

/--
Under a left root rotation, the sector of the root that is demoted gains one
level. This is the reverse of `right_externalDepth_promotedSector`.
-/
theorem left_externalDepth_demotedSector
    {lower demoted promoted upper position : ℕ}
    (a : BST lower demoted)
    (b : BST (demoted + 1) promoted)
    (c : BST (promoted + 1) upper)
    (hPosition : position ≤ 2 * demoted + 1) :
    (externalDepth (.node a (.node b c)) position).succ =
      externalDepth (.node (.node a b) c) position :=
  right_externalDepth_promotedSector a b c hPosition

/--
Under a left root rotation, depths in the middle sector are unchanged. This
sector is exactly the external-position interval of `b`.
-/
theorem left_externalDepth_middleSector
    {lower demoted promoted upper position : ℕ}
    (a : BST lower demoted)
    (b : BST (demoted + 1) promoted)
    (c : BST (promoted + 1) upper)
    (hDemoted : 2 * demoted + 1 < position)
    (hPromoted : position < 2 * promoted + 1) :
    externalDepth (.node a (.node b c)) position =
      externalDepth (.node (.node a b) c) position :=
  (right_externalDepth_middleSector a b c hDemoted hPromoted).symm

/--
Under a left root rotation, the sector of the child that is promoted loses one
level. This is the reverse of `right_externalDepth_demotedSector`.
-/
theorem left_externalDepth_promotedSector
    {lower demoted promoted upper position : ℕ}
    (a : BST lower demoted)
    (b : BST (demoted + 1) promoted)
    (c : BST (promoted + 1) upper)
    (hPosition : 2 * promoted + 1 ≤ position) :
    (externalDepth (.node (.node a b) c) position).succ =
      externalDepth (.node a (.node b c)) position :=
  right_externalDepth_demotedSector a b c hPosition

end Splay.Tree.BST.RootRotation
