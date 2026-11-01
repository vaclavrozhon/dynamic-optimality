import Splay.Accounting.LocalBendGeometry

namespace Splay.Accounting.WholeSplayTemporaryRootCreation

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical
open Splay.Accounting.LocalBendGeometry

/-!
Root-rotation creation formulae with no temporary-snapshot assumptions.

Every theorem below takes the relevant `heavyBranch` equations explicitly.
The conclusions isolate only incoming-edge changes of the original children,
plus the one newly assembled hanging node in the zig-zig cases.  The incoming
edge at the root of the rotated fragment remains arbitrary.
-/

/--
For a root zig from the left, every newly created bend comes from giving the
promoted key's original right child an incoming-left edge.
-/
theorem zigFromLeft_created_subset_baseIncomingDelta
    {n lower promoted demoted upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower promoted)
    (b : BST (promoted + 1) demoted)
    (c : BST (demoted + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (beforeRoot :
      (({
        lower := lower
        root := demoted
        upper := upper
        left := .node a b
        right := c
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left)
    (beforePromoted :
      (({
        lower := lower
        root := promoted
        upper := demoted
        left := a
        right := b
        upper_le_n := by
          have bounds := c.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterRoot :
      (({
        lower := lower
        root := promoted
        upper := upper
        left := a
        right := .node b c
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterDemoted :
      (({
        lower := promoted + 1
        root := demoted
        upper := upper
        left := b
        right := c
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left) :
    (bendsFrom snapshot
        (.node a (.node b c)) upper_le_n incoming \
      bendsFrom snapshot
        (.node (.node a b) c) upper_le_n incoming) ⊆
      (bendsFrom snapshot b (by
          have bounds := c.lower_le_upper
          omega) (some .left) \
        bendsFrom snapshot b (by
          have bounds := c.lower_le_upper
          omega) none) := by
  have beforeDecomposition :
      bendsFrom snapshot
          (.node (.node a b) c) upper_le_n incoming =
        bendAt ⟨demoted, by
            have bounds := c.lower_le_upper
            omega⟩ incoming .left ∪
          bendsFrom snapshot a (by
            have bounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have bounds := c.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c upper_le_n none := by
    simp only [bendsFrom]
    rw [beforeRoot, beforePromoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  have afterDecomposition :
      bendsFrom snapshot
          (.node a (.node b c)) upper_le_n incoming =
        bendsFrom snapshot a (by
            have bounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have bounds := c.lower_le_upper
            omega) (some .left) ∪
          bendsFrom snapshot c upper_le_n none := by
    simp only [bendsFrom]
    rw [afterRoot, afterDemoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  intro identity created
  rw [afterDecomposition, beforeDecomposition] at created
  simp only [Finset.mem_sdiff, Finset.mem_union] at created ⊢
  tauto

/--
For a root zig from the right, every newly created bend comes from giving
the promoted key's original left child an incoming-right edge.
-/
theorem zigFromRight_created_subset_baseIncomingDelta
    {n lower demoted promoted upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower demoted)
    (b : BST (demoted + 1) promoted)
    (c : BST (promoted + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (beforeRoot :
      (({
        lower := lower
        root := demoted
        upper := upper
        left := a
        right := .node b c
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .right)
    (beforePromoted :
      (({
        lower := demoted + 1
        root := promoted
        upper := upper
        left := b
        right := c
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterRoot :
      (({
        lower := lower
        root := promoted
        upper := upper
        left := .node a b
        right := c
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterDemoted :
      (({
        lower := lower
        root := demoted
        upper := promoted
        left := a
        right := b
        upper_le_n := by
          have bounds := c.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .right) :
    (bendsFrom snapshot
        (.node (.node a b) c) upper_le_n incoming \
      bendsFrom snapshot
        (.node a (.node b c)) upper_le_n incoming) ⊆
      (bendsFrom snapshot b (by
          have bounds := c.lower_le_upper
          omega) (some .right) \
        bendsFrom snapshot b (by
          have bounds := c.lower_le_upper
          omega) none) := by
  have beforeDecomposition :
      bendsFrom snapshot
          (.node a (.node b c)) upper_le_n incoming =
        bendAt ⟨demoted, by
            have bounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            omega⟩ incoming .right ∪
          bendsFrom snapshot a (by
            have bounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have bounds := c.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c upper_le_n none := by
    simp only [bendsFrom]
    rw [beforeRoot, beforePromoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  have afterDecomposition :
      bendsFrom snapshot
          (.node (.node a b) c) upper_le_n incoming =
        bendsFrom snapshot a (by
            have bounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have bounds := c.lower_le_upper
            omega) (some .right) ∪
          bendsFrom snapshot c upper_le_n none := by
    simp only [bendsFrom]
    rw [afterRoot, afterDemoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  intro identity created
  rw [afterDecomposition, beforeDecomposition] at created
  simp only [Finset.mem_sdiff, Finset.mem_union] at created ⊢
  tauto

/--
For a root left-right zig-zag, every creation is one of the two base-child
incoming-edge deltas.
-/
theorem zigZagLeftRight_created_subset_baseIncomingDeltas
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (beforeRoot :
      (({
        lower := lower
        root := third
        upper := upper
        left := .node a (.node b c)
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left)
    (beforeFirst :
      (({
        lower := lower
        root := first
        upper := third
        left := a
        right := .node b c
        upper_le_n := by
          have bounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .right)
    (beforePromoted :
      (({
        lower := first + 1
        root := second
        upper := third
        left := b
        right := c
        upper_le_n := by
          have bounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterRoot :
      (({
        lower := lower
        root := second
        upper := upper
        left := .node a b
        right := .node c d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterFirst :
      (({
        lower := lower
        root := first
        upper := second
        left := a
        right := b
        upper_le_n := by
          have cBounds := c.lower_le_upper
          have dBounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .right)
    (afterThird :
      (({
        lower := second + 1
        root := third
        upper := upper
        left := c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left) :
    (bendsFrom snapshot
        (.node (.node a b) (.node c d)) upper_le_n incoming \
      bendsFrom snapshot
        (.node (.node a (.node b c)) d) upper_le_n incoming) ⊆
      ((bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .right) \
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none) ∪
        (bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .left) \
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none)) := by
  have beforeDecomposition :
      bendsFrom snapshot
          (.node (.node a (.node b c)) d) upper_le_n incoming =
        bendAt ⟨third, by
            have bounds := d.lower_le_upper
            omega⟩ incoming .left ∪
          bendAt ⟨first, by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega⟩ (some .left) .right ∪
          bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot d upper_le_n none := by
    simp only [bendsFrom]
    rw [beforeRoot, beforeFirst, beforePromoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  have afterDecomposition :
      bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming =
        bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .right) ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .left) ∪
          bendsFrom snapshot d upper_le_n none := by
    simp only [bendsFrom]
    rw [afterRoot, afterFirst, afterThird]
    simp only [childIncoming, bendAt, Turns]
    simp
  intro identity created
  rw [afterDecomposition, beforeDecomposition] at created
  simp only [Finset.mem_sdiff, Finset.mem_union] at created ⊢
  tauto

/--
For a root right-left zig-zag, every creation is one of the same two
base-child incoming-edge deltas.
-/
theorem zigZagRightLeft_created_subset_baseIncomingDeltas
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (beforeRoot :
      (({
        lower := lower
        root := first
        upper := upper
        left := a
        right := .node (.node b c) d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .right)
    (beforeThird :
      (({
        lower := first + 1
        root := third
        upper := upper
        left := .node b c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left)
    (beforePromoted :
      (({
        lower := first + 1
        root := second
        upper := third
        left := b
        right := c
        upper_le_n := by
          have bounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterRoot :
      (({
        lower := lower
        root := second
        upper := upper
        left := .node a b
        right := .node c d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterFirst :
      (({
        lower := lower
        root := first
        upper := second
        left := a
        right := b
        upper_le_n := by
          have cBounds := c.lower_le_upper
          have dBounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .right)
    (afterThird :
      (({
        lower := second + 1
        root := third
        upper := upper
        left := c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left) :
    (bendsFrom snapshot
        (.node (.node a b) (.node c d)) upper_le_n incoming \
      bendsFrom snapshot
        (.node a (.node (.node b c) d)) upper_le_n incoming) ⊆
      ((bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .right) \
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none) ∪
        (bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .left) \
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none)) := by
  have beforeDecomposition :
      bendsFrom snapshot
          (.node a (.node (.node b c) d)) upper_le_n incoming =
        bendAt ⟨first, by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega⟩ incoming .right ∪
          bendAt ⟨third, by
            have bounds := d.lower_le_upper
            omega⟩ (some .right) .left ∪
          bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot d upper_le_n none := by
    simp only [bendsFrom]
    rw [beforeRoot, beforeThird, beforePromoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  have afterDecomposition :
      bendsFrom snapshot
          (.node (.node a b) (.node c d)) upper_le_n incoming =
        bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .right) ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .left) ∪
          bendsFrom snapshot d upper_le_n none := by
    simp only [bendsFrom]
    rw [afterRoot, afterFirst, afterThird]
    simp only [childIncoming, bendAt, Turns]
    simp
  intro identity created
  rw [afterDecomposition, beforeDecomposition] at created
  simp only [Finset.mem_sdiff, Finset.mem_union] at created ⊢
  tauto

/--
For a root left-left zig-zig, creations are confined to the original right
base child's incoming-left delta and to bends introduced by assembling the
new hanging node over `c` and `d`.
-/
theorem zigZigLeft_created_subset_baseAndHangingDeltas
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (beforeRoot :
      (({
        lower := lower
        root := third
        upper := upper
        left := .node (.node a b) c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left)
    (beforeSecond :
      (({
        lower := lower
        root := second
        upper := third
        left := .node a b
        right := c
        upper_le_n := by
          have bounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .left)
    (beforePromoted :
      (({
        lower := lower
        root := first
        upper := second
        left := a
        right := b
        upper_le_n := by
          have cBounds := c.lower_le_upper
          have dBounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterRoot :
      (({
        lower := lower
        root := first
        upper := upper
        left := a
        right := .node b (.node c d)
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterSecond :
      (({
        lower := first + 1
        root := second
        upper := upper
        left := b
        right := .node c d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .left) :
    (bendsFrom snapshot
        (.node a (.node b (.node c d))) upper_le_n incoming \
      bendsFrom snapshot
        (.node (.node (.node a b) c) d) upper_le_n incoming) ⊆
      ((bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .left) \
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none) ∪
        (bendsFrom snapshot (.node c d) upper_le_n none \
          (bendsFrom snapshot c (by
                have bounds := d.lower_le_upper
                omega) none ∪
            bendsFrom snapshot d upper_le_n none))) := by
  have beforeDecomposition :
      bendsFrom snapshot
          (.node (.node (.node a b) c) d) upper_le_n incoming =
        bendAt ⟨third, by
            have bounds := d.lower_le_upper
            omega⟩ incoming .left ∪
          bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot d upper_le_n none := by
    simp only [bendsFrom]
    rw [beforeRoot, beforeSecond, beforePromoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  have afterSecondDecomposition :
      bendsFrom snapshot
          (.node b (.node c d)) upper_le_n none =
        bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .left) ∪
          bendsFrom snapshot (.node c d) upper_le_n none := by
    rw [bendsFrom]
    rw [afterSecond]
    simp [childIncoming, bendAt, Turns]
  have afterDecomposition :
      bendsFrom snapshot
          (.node a (.node b (.node c d))) upper_le_n incoming =
        bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) (some .left) ∪
          bendsFrom snapshot (.node c d) upper_le_n none := by
    rw [bendsFrom]
    rw [afterRoot]
    simp only [childIncoming, bendAt, Turns]
    simp
    rw [afterSecondDecomposition]
  intro identity created
  rw [afterDecomposition, beforeDecomposition] at created
  simp only [Finset.mem_sdiff, Finset.mem_union] at created ⊢
  tauto

/--
For a root right-right zig-zig, creations are confined to the original left
base child's incoming-right delta and to bends introduced by assembling the
new hanging node over `a` and `b`.
-/
theorem zigZigRight_created_subset_baseAndHangingDeltas
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first)
    (b : BST (first + 1) second)
    (c : BST (second + 1) third)
    (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n)
    (incoming : Option TernaryBranch)
    (beforeRoot :
      (({
        lower := lower
        root := first
        upper := upper
        left := a
        right := .node b (.node c d)
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .right)
    (beforeSecond :
      (({
        lower := first + 1
        root := second
        upper := upper
        left := b
        right := .node c d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .right)
    (beforePromoted :
      (({
        lower := second + 1
        root := third
        upper := upper
        left := c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterRoot :
      (({
        lower := lower
        root := third
        upper := upper
        left := .node (.node a b) c
        right := d
        upper_le_n := upper_le_n
      } : AtNode n).heavyBranch snapshot) = .middle)
    (afterSecond :
      (({
        lower := lower
        root := second
        upper := third
        left := .node a b
        right := c
        upper_le_n := by
          have bounds := d.lower_le_upper
          omega
      } : AtNode n).heavyBranch snapshot) = .right) :
    (bendsFrom snapshot
        (.node (.node (.node a b) c) d) upper_le_n incoming \
      bendsFrom snapshot
        (.node a (.node b (.node c d))) upper_le_n incoming) ⊆
      ((bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .right) \
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none) ∪
        (bendsFrom snapshot (.node a b) (by
              have cBounds := c.lower_le_upper
              have dBounds := d.lower_le_upper
              omega) none \
          (bendsFrom snapshot a (by
                have bBounds := b.lower_le_upper
                have cBounds := c.lower_le_upper
                have dBounds := d.lower_le_upper
                omega) none ∪
            bendsFrom snapshot b (by
                have cBounds := c.lower_le_upper
                have dBounds := d.lower_le_upper
                omega) none))) := by
  have beforeDecomposition :
      bendsFrom snapshot
          (.node a (.node b (.node c d))) upper_le_n incoming =
        bendAt ⟨first, by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega⟩ incoming .right ∪
          bendsFrom snapshot a (by
            have bBounds := b.lower_le_upper
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot b (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot d upper_le_n none := by
    simp only [bendsFrom]
    rw [beforeRoot, beforeSecond, beforePromoted]
    simp only [childIncoming, bendAt, Turns]
    simp
  have afterSecondDecomposition :
      bendsFrom snapshot
          (.node (.node a b) c) (by
            have bounds := d.lower_le_upper
            omega) none =
        bendsFrom snapshot (.node a b) (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .right) := by
    rw [bendsFrom]
    rw [afterSecond]
    simp [childIncoming, bendAt, Turns]
  have afterDecomposition :
      bendsFrom snapshot
          (.node (.node (.node a b) c) d) upper_le_n incoming =
        bendsFrom snapshot (.node a b) (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) none ∪
          bendsFrom snapshot c (by
            have bounds := d.lower_le_upper
            omega) (some .right) ∪
          bendsFrom snapshot d upper_le_n none := by
    rw [bendsFrom]
    rw [afterRoot]
    simp only [childIncoming, bendAt, Turns]
    simp
    rw [afterSecondDecomposition]
    ac_rfl
  intro identity created
  rw [afterDecomposition, beforeDecomposition] at created
  simp only [Finset.mem_sdiff, Finset.mem_union] at created ⊢
  tauto

end Splay.Accounting.WholeSplayTemporaryRootCreation
