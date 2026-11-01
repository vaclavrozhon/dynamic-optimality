import Splay.Accounting.InternalPhasePairingAlignment

namespace Splay.Accounting

open Splay.Lazy
open Splay.Lazy.Canonical
open Splay.Rank
open Splay.Tree.BST

namespace HeapChildPairing

/-- The two sequential article phases remove different candidates. -/
theorem loserBranch_first_ne_second_for_article
    (heavy : TernaryBranch) :
    loserBranch heavy .first ≠ loserBranch heavy .second := by
  cases heavy <;> decide

/-- The two canonical phase losers at one node are distinct. -/
theorem phase_losers_ne
    {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    (ofNode snapshot node .first).loser ≠
      (ofNode snapshot node .second).loser := by
  intro equal
  have branchEqual :
      loserBranch (node.heavyBranch snapshot) .first =
        loserBranch (node.heavyBranch snapshot) .second :=
    (branchMin_injective snapshot node) equal
  exact loserBranch_first_ne_second_for_article _ branchEqual

end HeapChildPairing

/-- In a left zig-zig the candidate triple is the final three-child run of
the local four-child bottom-up chunk. -/
theorem rootHeavyPathChildrenBottomUp_zigZigLeft_eq_cons_candidates
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first) (b : BST (first + 1) second)
    (c : BST (second + 1) third) (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n) (first_lt_n : first < n)
    (rankZero : snapshot.rank (valuePos ⟨first, first_lt_n⟩) = 0)
    (depth : ℕ) :
    let before : BST lower upper := .node (.node (.node a b) c) d
    let endpointNode : AtNode n := {
      lower := second + 1
      root := third
      upper := upper
      left := c
      right := d
      upper_le_n := upper_le_n
    }
    ∃ extra,
      rootHeavyPathChildrenBottomUp snapshot before upper_le_n first depth =
        extra :: HeapChildPairing.candidates snapshot endpointNode := by
  dsimp only
  let outer : AtNode n := {
    lower := lower
    root := third
    upper := upper
    left := .node (.node a b) c
    right := d
    upper_le_n := upper_le_n
  }
  let parent : AtNode n := {
    lower := lower
    root := second
    upper := third
    left := .node a b
    right := c
    upper_le_n := by
      have := d.lower_le_upper
      omega
  }
  have firstLtSecond : first < second := by
    have := b.lower_le_upper
    omega
  have secondLtThird : second < third := by
    have := c.lower_le_upper
    omega
  have thirdLtUpper : third < upper := by
    have := d.lower_le_upper
    omega
  have firstLtThird : first < third := by omega
  have firstNeSecond : first ≠ second := by omega
  have firstNeThird : first ≠ third := by omega
  have notSecondLtFirst : ¬ second < first := by omega
  have notThirdLtFirst : ¬ third < first := by omega
  have outerHeavy := heavyBranch_eq_searchBranch snapshot outer first
    (by dsimp [outer]; have := a.lower_le_upper; omega)
    (by dsimp [outer]; omega)
    (by dsimp [outer]; omega) first_lt_n rankZero
  have parentHeavy := heavyBranch_eq_searchBranch snapshot parent first
    (by dsimp [parent]; have := a.lower_le_upper; omega)
    (by dsimp [parent]; omega)
    (by dsimp [parent]; omega) first_lt_n rankZero
  refine ⟨parent.branchMin snapshot .middle, ?_⟩
  simp [rootHeavyPathChildrenBottomUp, rootHeavyPathEdgesBottomUp,
    rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
    RootHeavyPathCell.fullTopDownEdges, rootHeavyPathCellAt,
    edgesAtNode, lightBranches, allBranches, hitSide,
    outer, parent, outerHeavy, parentHeavy, firstLtSecond, firstLtThird,
    firstNeSecond, firstNeThird, notSecondLtFirst, notThirdLtFirst,
    HeapChildPairing.candidates, edgeFor]
  rfl

/-- In a right zig-zig the candidate triple occurs in the mirrored order as
the final three-child run of the local four-child bottom-up chunk. -/
theorem rootHeavyPathChildrenBottomUp_zigZigRight_eq_cons_candidates_reverse
    {n lower first second third upper : ℕ}
    (snapshot : Snapshot n)
    (a : BST lower first) (b : BST (first + 1) second)
    (c : BST (second + 1) third) (d : BST (third + 1) upper)
    (upper_le_n : upper ≤ n) (third_lt_n : third < n)
    (rankZero : snapshot.rank (valuePos ⟨third, third_lt_n⟩) = 0)
    (depth : ℕ) :
    let before : BST lower upper := .node a (.node b (.node c d))
    let endpointNode : AtNode n := {
      lower := lower
      root := first
      upper := second
      left := a
      right := b
      upper_le_n := by
        have := c.lower_le_upper
        have := d.lower_le_upper
        omega
    }
    ∃ extra,
      rootHeavyPathChildrenBottomUp snapshot before upper_le_n third depth =
        extra :: (HeapChildPairing.candidates snapshot endpointNode).reverse := by
  dsimp only
  let outer : AtNode n := {
    lower := lower
    root := first
    upper := upper
    left := a
    right := .node b (.node c d)
    upper_le_n := upper_le_n
  }
  let parent : AtNode n := {
    lower := first + 1
    root := second
    upper := upper
    left := b
    right := .node c d
    upper_le_n := upper_le_n
  }
  have secondLtThird : second < third := by
    have := c.lower_le_upper
    omega
  have firstLtThird : first < third := by
    have := b.lower_le_upper
    omega
  have thirdNeFirst : third ≠ first := by omega
  have thirdNeSecond : third ≠ second := by omega
  have notThirdLtFirst : ¬ third < first := by omega
  have notThirdLtSecond : ¬ third < second := by omega
  have outerHeavy := heavyBranch_eq_searchBranch snapshot outer third
    (by dsimp [outer]; have := a.lower_le_upper; omega)
    (by dsimp [outer]; have := d.lower_le_upper; omega)
    (by dsimp [outer]; omega) third_lt_n rankZero
  have parentHeavy := heavyBranch_eq_searchBranch snapshot parent third
    (by dsimp [parent]; omega)
    (by dsimp [parent]; have := d.lower_le_upper; omega)
    (by dsimp [parent]; omega) third_lt_n rankZero
  refine ⟨parent.branchMin snapshot .middle, ?_⟩
  simp [rootHeavyPathChildrenBottomUp, rootHeavyPathEdgesBottomUp,
    rootHeavyPathEdgesTopDown, rootHeavyPathCellsTopDown,
    rootHeavyPathCellAt, edgesAtNode, lightBranches, allBranches, hitSide,
    outer, parent, outerHeavy, parentHeavy, secondLtThird, firstLtThird,
    thirdNeFirst, thirdNeSecond, notThirdLtFirst, notThirdLtSecond,
    HeapChildPairing.candidates, edgeFor]
  rfl

set_option linter.unusedVariables false in
/--
Both sequential manuscript pairings of one concrete zig-zig, sharing the
same winner and the same underlying three-candidate configuration.
-/
inductive ZigZigBothPairingEndpointsAt {n : ℕ} (snapshot : Snapshot n) :
    {depth key lower upper : ℕ} →
      BST lower upper → BST lower upper →
      Interface.Element n → Interface.Element n →
      Interface.Element n → Prop
  | zigZigLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper)
      (upper_le_n : upper ≤ n) :
      ZigZigBothPairingEndpointsAt snapshot
        (depth := 0) (key := first)
        (.node (.node (.node a b) c) d)
        (.node a (.node b (.node c d)))
        (HeapChildPairing.ofNode snapshot {
          lower := second + 1
          root := third
          upper := upper
          left := c
          right := d
          upper_le_n := upper_le_n
        } .first).winner
        (HeapChildPairing.ofNode snapshot {
          lower := second + 1
          root := third
          upper := upper
          left := c
          right := d
          upper_le_n := upper_le_n
        } .first).loser
        (HeapChildPairing.ofNode snapshot {
          lower := second + 1
          root := third
          upper := upper
          left := c
          right := d
          upper_le_n := upper_le_n
        } .second).loser
  | zigZigRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper)
      (upper_le_n : upper ≤ n)
      (second_le_n : second ≤ n) :
      ZigZigBothPairingEndpointsAt snapshot
        (depth := 0) (key := third)
        (.node a (.node b (.node c d)))
        (.node (.node (.node a b) c) d)
        (HeapChildPairing.ofNode snapshot {
          lower := lower
          root := first
          upper := second
          left := a
          right := b
          upper_le_n := second_le_n
        } .first).winner
        (HeapChildPairing.ofNode snapshot {
          lower := lower
          root := first
          upper := second
          left := a
          right := b
          upper_le_n := second_le_n
        } .first).loser
        (HeapChildPairing.ofNode snapshot {
          lower := lower
          root := first
          upper := second
          left := a
          right := b
          upper_le_n := second_le_n
        } .second).loser
  | leftContext
      {depth key lower root upper : ℕ}
      {before after : BST lower root}
      {winner firstLoser secondLoser : Interface.Element n}
      (inside : ZigZigBothPairingEndpointsAt snapshot
        (depth := depth) (key := key) before after
        winner firstLoser secondLoser)
      (right : BST (root + 1) upper) :
      ZigZigBothPairingEndpointsAt snapshot
        (depth := depth.succ) (key := key)
        (.node before right) (.node after right)
        winner firstLoser secondLoser
  | rightContext
      {depth key lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      {winner firstLoser secondLoser : Interface.Element n}
      (inside : ZigZigBothPairingEndpointsAt snapshot
        (depth := depth) (key := key) before after
        winner firstLoser secondLoser) :
      ZigZigBothPairingEndpointsAt snapshot
        (depth := depth.succ) (key := key)
        (.node left before) (.node left after)
        winner firstLoser secondLoser

namespace ZigZigBothPairingEndpointsAt

/-- Project the jointly chosen first phase. -/
theorem first {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser) :
    ZigZigPairingEndpointsAt snapshot .first
      (depth := depth) (key := key) before after winner firstLoser := by
  induction both with
  | zigZigLeft a b c d upper_le_n =>
      exact .zigZigLeft a b c d upper_le_n .first
  | zigZigRight a b c d upper_le_n second_le_n =>
      exact .zigZigRight a b c d upper_le_n second_le_n .first
  | leftContext inside right ih => exact .leftContext ih right
  | rightContext left inside ih => exact .rightContext left ih

/-- Project the jointly chosen second phase. -/
theorem second {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser) :
    ZigZigPairingEndpointsAt snapshot .second
      (depth := depth) (key := key) before after winner secondLoser := by
  induction both with
  | zigZigLeft a b c d upper_le_n =>
      exact .zigZigLeft a b c d upper_le_n .second
  | zigZigRight a b c d upper_le_n second_le_n =>
      exact .zigZigRight a b c d upper_le_n second_le_n .second
  | leftContext inside right ih => exact .leftContext ih right
  | rightContext left inside ih => exact .rightContext left ih

/-- The first and second phase remove different heap children. -/
theorem losers_ne {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser) : firstLoser ≠ secondLoser := by
  induction both with
  | zigZigLeft a b c d upper_le_n =>
      exact HeapChildPairing.phase_losers_ne snapshot _
  | zigZigRight a b c d upper_le_n second_le_n =>
      exact HeapChildPairing.phase_losers_ne snapshot _
  | leftContext inside right ih => exact ih
  | rightContext left inside ih => exact ih

/-- The accessed key stays inside every context carrying the local zig-zig. -/
theorem key_bounds {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser) :
    lower ≤ key ∧ key < upper := by
  induction both with
  | zigZigLeft a b c d upper_le_n =>
      have := a.lower_le_upper
      have := b.lower_le_upper
      have := c.lower_le_upper
      have := d.lower_le_upper
      omega
  | zigZigRight a b c d upper_le_n second_le_n =>
      have := a.lower_le_upper
      have := b.lower_le_upper
      have := c.lower_le_upper
      have := d.lower_le_upper
      omega
  | leftContext inside right ih =>
      have := right.lower_le_upper
      omega
  | rightContext left inside ih =>
      have := left.lower_le_upper
      omega

private theorem isSegment_append_right
    {alpha : Type*} {inside whole : List alpha}
    (segment : IsSegment inside whole) (suffix : List alpha) :
    IsSegment inside (whole ++ suffix) := by
  obtain ⟨front, back, rfl⟩ := segment
  exact ⟨front, back ++ suffix, by simp [List.append_assoc]⟩

/--
The article's three candidates occur as one actual contiguous run in the
bottom-up order of the root-heavy path.  This is stronger than merely knowing
that all three endpoints belong to the same four-child group: it preserves
the order needed by the two sequential `Pass` operations.
-/
theorem sequential_geometry_on_rootHeavyPath
    {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (startDepth : ℕ) :
    ∃ candidates,
      IsSegment candidates
          (rootHeavyPathChildrenBottomUp snapshot before upper_le_n key
            startDepth) ∧
        Interface.Adjacent candidates winner firstLoser ∧
        Interface.Adjacent (candidates.erase firstLoser)
          winner secondLoser ∧
        candidates.Perm [winner, firstLoser, secondLoser] := by
  induction both generalizing startDepth with
  | zigZigLeft a b c d localUpper =>
      obtain ⟨extra, chunkEq⟩ :=
        rootHeavyPathChildrenBottomUp_zigZigLeft_eq_cons_candidates
          snapshot a b c d upper_le_n key_lt_n rankZero startDepth
      refine ⟨HeapChildPairing.candidates snapshot _, ?_,
        HeapChildPairing.first_adjacent_candidates snapshot _,
        HeapChildPairing.second_adjacent_after_erase_first snapshot _,
        HeapChildPairing.candidates_perm_phaseEndpoints snapshot _⟩
      exact ⟨[extra], [], by simpa using chunkEq⟩
  | zigZigRight a b c d localUpper second_le_n =>
      obtain ⟨extra, chunkEq⟩ :=
        rootHeavyPathChildrenBottomUp_zigZigRight_eq_cons_candidates_reverse
          snapshot a b c d upper_le_n key_lt_n rankZero startDepth
      refine ⟨(HeapChildPairing.candidates snapshot _).reverse, ?_,
        HeapChildPairing.first_adjacent_candidates_reverse snapshot _,
        HeapChildPairing.second_adjacent_after_erase_first_reverse snapshot _,
        (List.reverse_perm _).trans
          (HeapChildPairing.candidates_perm_phaseEndpoints snapshot _)⟩
      exact ⟨[extra], [], by simpa using chunkEq⟩
  | @leftContext depth key lower root upper before after winner firstLoser
      secondLoser inside right ih =>
      have childUpper : root ≤ n := by
        have := right.lower_le_upper
        omega
      obtain ⟨candidates, segment, firstAdjacent, secondAdjacent, perm⟩ :=
        ih childUpper key_lt_n rankZero (startDepth + 1)
      refine ⟨candidates, ?_, firstAdjacent, secondAdjacent, perm⟩
      rw [rootHeavyPathChildrenBottomUp_leftContext snapshot before right
        upper_le_n inside.key_bounds.2 startDepth]
      exact isSegment_append_right segment _
  | @rightContext depth key lower root upper left before after winner firstLoser
      secondLoser inside ih =>
      obtain ⟨candidates, segment, firstAdjacent, secondAdjacent, perm⟩ :=
        ih upper_le_n key_lt_n rankZero (startDepth + 1)
      refine ⟨candidates, ?_, firstAdjacent, secondAdjacent, perm⟩
      rw [rootHeavyPathChildrenBottomUp_rightContext snapshot left before
        upper_le_n (by have bounds := inside.key_bounds; omega) startDepth]
      exact isSegment_append_right segment _

/-- More precise prefix form of the same geometry: the one unused child is
first, followed by the three candidates; only enclosing cells may follow. -/
theorem sequential_geometry_at_rootHeavyPath_prefix
    {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    (startDepth : ℕ) :
    ∃ extra candidates suffix,
      rootHeavyPathChildrenBottomUp snapshot before upper_le_n key
          startDepth = extra :: candidates ++ suffix ∧
        candidates.length = 3 ∧
        Interface.Adjacent candidates winner firstLoser ∧
        Interface.Adjacent (candidates.erase firstLoser)
          winner secondLoser ∧
        candidates.Perm [winner, firstLoser, secondLoser] := by
  induction both generalizing startDepth with
  | zigZigLeft a b c d localUpper =>
      obtain ⟨extra, chunkEq⟩ :=
        rootHeavyPathChildrenBottomUp_zigZigLeft_eq_cons_candidates
          snapshot a b c d upper_le_n key_lt_n rankZero startDepth
      refine ⟨extra, HeapChildPairing.candidates snapshot _, [], ?_, ?_,
        HeapChildPairing.first_adjacent_candidates snapshot _,
        HeapChildPairing.second_adjacent_after_erase_first snapshot _,
        HeapChildPairing.candidates_perm_phaseEndpoints snapshot _⟩
      · simpa using chunkEq
      · simp [HeapChildPairing.candidates, allBranches]
  | zigZigRight a b c d localUpper second_le_n =>
      obtain ⟨extra, chunkEq⟩ :=
        rootHeavyPathChildrenBottomUp_zigZigRight_eq_cons_candidates_reverse
          snapshot a b c d upper_le_n key_lt_n rankZero startDepth
      refine ⟨extra, (HeapChildPairing.candidates snapshot _).reverse, [],
        ?_, ?_,
        HeapChildPairing.first_adjacent_candidates_reverse snapshot _,
        HeapChildPairing.second_adjacent_after_erase_first_reverse snapshot _,
        (List.reverse_perm _).trans
          (HeapChildPairing.candidates_perm_phaseEndpoints snapshot _)⟩
      · simpa using chunkEq
      · simp [HeapChildPairing.candidates, allBranches]
  | @leftContext depth key lower root upper before after winner firstLoser
      secondLoser inside right ih =>
      have childUpper : root ≤ n := by
        have := right.lower_le_upper
        omega
      obtain ⟨extra, candidates, suffix, childEq, candidateLength,
          firstAdjacent, secondAdjacent, perm⟩ :=
        ih childUpper key_lt_n rankZero (startDepth + 1)
      refine ⟨extra, candidates,
        suffix ++ (rootHeavyPathCellAt snapshot {
          lower := lower
          root := root
          upper := upper
          left := before
          right := right
          upper_le_n := upper_le_n
        } startDepth key).fullBottomUpEdges.map Edge.child,
        ?_, candidateLength, firstAdjacent, secondAdjacent, perm⟩
      rw [rootHeavyPathChildrenBottomUp_leftContext snapshot before right
        upper_le_n inside.key_bounds.2 startDepth, childEq]
      simp [List.append_assoc]
  | @rightContext depth key lower root upper left before after winner firstLoser
      secondLoser inside ih =>
      obtain ⟨extra, candidates, suffix, childEq, candidateLength,
          firstAdjacent, secondAdjacent, perm⟩ :=
        ih upper_le_n key_lt_n rankZero (startDepth + 1)
      refine ⟨extra, candidates,
        suffix ++ (rootHeavyPathCellAt snapshot {
          lower := lower
          root := root
          upper := upper
          left := left
          right := before
          upper_le_n := upper_le_n
        } startDepth key).fullBottomUpEdges.map Edge.child,
        ?_, candidateLength, firstAdjacent, secondAdjacent, perm⟩
      rw [rootHeavyPathChildrenBottomUp_rightContext snapshot left before
        upper_le_n (by have bounds := inside.key_bounds; omega) startDepth,
        childEq]
      simp [List.append_assoc]

/--
The exact local sequential geometry from the manuscript: the first pair is
adjacent, and erasing its loser makes the second pair adjacent.
-/
theorem sequential_adjacency {n : ℕ} {snapshot : Snapshot n}
    {depth key lower upper : ℕ} {before after : BST lower upper}
    {winner firstLoser secondLoser : Interface.Element n}
    (both : ZigZigBothPairingEndpointsAt snapshot
      (depth := depth) (key := key) before after
      winner firstLoser secondLoser) :
    ∃ candidates,
      Interface.Adjacent candidates winner firstLoser ∧
        Interface.Adjacent (candidates.erase firstLoser)
          winner secondLoser ∧
        candidates.Perm [winner, firstLoser, secondLoser] := by
  induction both with
  | zigZigLeft a b c d upper_le_n =>
      exact ⟨HeapChildPairing.candidates snapshot _,
        HeapChildPairing.first_adjacent_candidates snapshot _,
        HeapChildPairing.second_adjacent_after_erase_first snapshot _,
        HeapChildPairing.candidates_perm_phaseEndpoints snapshot _⟩
  | zigZigRight a b c d upper_le_n second_le_n =>
      exact ⟨(HeapChildPairing.candidates snapshot _).reverse,
        HeapChildPairing.first_adjacent_candidates_reverse snapshot _,
        HeapChildPairing.second_adjacent_after_erase_first_reverse snapshot _,
        (List.reverse_perm _).trans
          (HeapChildPairing.candidates_perm_phaseEndpoints snapshot _)⟩
  | leftContext inside right ih => exact ih
  | rightContext left inside ih => exact ih

/-- Every concrete true double orientation has a joint two-phase witness. -/
theorem exists_of_orientation
    {n : ℕ} (snapshot : Snapshot n)
    {depth key lower upper : ℕ} {before after : BST lower upper}
    (orientation : DoubleOrientationAt true
      (depth := depth) (key := key) before after)
    (upper_le_n : upper ≤ n) :
    ∃ winner firstLoser secondLoser,
      ZigZigBothPairingEndpointsAt snapshot
        (depth := depth) (key := key) before after
        winner firstLoser secondLoser := by
  generalize flag_eq : true = flag at orientation
  induction orientation with
  | zigZigLeft a b c d =>
      exact ⟨_, _, _, .zigZigLeft a b c d upper_le_n⟩
  | @zigZigRight lower first second third upper a b c d =>
      have second_le_n : second ≤ n := by
        have := c.lower_le_upper
        have := d.lower_le_upper
        omega
      exact ⟨_, _, _, .zigZigRight a b c d upper_le_n second_le_n⟩
  | zigZagLeftRight => contradiction
  | zigZagRightLeft => contradiction
  | leftContext orientation right ih =>
      obtain ⟨winner, firstLoser, secondLoser, inside⟩ :=
        ih (by have := right.lower_le_upper; omega) flag_eq
      exact ⟨winner, firstLoser, secondLoser, .leftContext inside right⟩
  | rightContext left orientation ih =>
      obtain ⟨winner, firstLoser, secondLoser, inside⟩ :=
        ih upper_le_n flag_eq
      exact ⟨winner, firstLoser, secondLoser, .rightContext left inside⟩

end ZigZigBothPairingEndpointsAt

namespace ZigZigPairingEndpointsAt

/-- Package one phase's two local support witnesses at the next two hits. -/
theorem heapChildren_supportedIn_take
    {n depth key lower upper : ℕ} {snapshot : Snapshot n}
    {phase : PairingPhase}
    {before after : BST lower upper} {winner loser : External n}
    (endpoints : ZigZigPairingEndpointsAt snapshot phase
      (depth := depth) (key := key) before after winner loser)
    (step : DoubleRotationAt depth key before after)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    HeapChildrenSupportedIn snapshot before upper_le_n
      ((before.searchPath key).dropLast.reverse.take 2) [winner, loser] := by
  have localSupport :=
    endpoints.heapChildren_supported upper_le_n 0 key_lt_n rankZero
  refine ⟨by simp, ?_, ?_⟩
  · have winnerNe : winner ≠ loser := by
      intro equal
      have rankLt := endpoints.rank_lt
      rw [equal] at rankLt
      exact Nat.lt_irrefl _ rankLt
    simp [winnerNe]
  · intro child childMember
    simp at childMember
    rcases childMember with rfl | rfl
    · obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
        localSupport.1
      exact ⟨edge, edgeMember, childEq,
        (DoubleRotationAt.mem_zigZigHitSupport_iff_mem_take_properAncestors
          (node := edge.attachmentKey) step).mp attachmentMember⟩
    · obtain ⟨edge, edgeMember, childEq, attachmentMember⟩ :=
        localSupport.2
      exact ⟨edge, edgeMember, childEq,
        (DoubleRotationAt.mem_zigZigHitSupport_iff_mem_take_properAncestors
          (node := edge.attachmentKey) step).mp attachmentMember⟩

end ZigZigPairingEndpointsAt

namespace SplayExecutionTranscript

/--
Joint first/second selections preserve that both phases of a zig-zig use the
same winner and the two sequential losers from one local configuration.
-/
inductive BothPhaseSelections {n : ℕ} (snapshot : Snapshot n) (key : ℕ) :
    {lower upper : ℕ} → {before after : BST lower upper} →
      {execution : SplayExecution key before after} →
      {kinds : List SplayStepKind} → {zig zigZig zigZag : ℕ} →
      SplayExecutionTranscript key execution kinds zig zigZig zigZag →
      List (List (External n)) → List (List (External n)) → Prop
  | done {lower upper : ℕ} {tree : BST lower upper}
      (root : tree.HasRoot key) :
      BothPhaseSelections snapshot key (.done root) [] []
  | zig {lower upper : ℕ} {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : Zig key before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {firstSelections secondSelections : List (List (External n))}
      (rest : BothPhaseSelections snapshot key tailTranscript
        firstSelections secondSelections) :
      BothPhaseSelections snapshot key (.zig step tail tailTranscript)
        firstSelections secondSelections
  | zigZig {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation : DoubleOrientationAt true
        (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {winner firstLoser secondLoser : External n}
      (endpoints : ZigZigBothPairingEndpointsAt snapshot
        (depth := depth) (key := key) before middle
        winner firstLoser secondLoser)
      {firstSelections secondSelections : List (List (External n))}
      (rest : BothPhaseSelections snapshot key tailTranscript
        firstSelections secondSelections) :
      BothPhaseSelections snapshot key
        (.zigZig step orientation tail tailTranscript)
        ([winner, firstLoser] :: firstSelections)
        ([winner, secondLoser] :: secondSelections)
  | zigZag {depth lower upper : ℕ}
      {before middle after : BST lower upper}
      {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
      (step : DoubleRotationAt depth key before middle)
      (orientation : DoubleOrientationAt false
        (depth := depth) (key := key) before middle)
      (tail : SplayExecution key middle after)
      (tailTranscript :
        SplayExecutionTranscript key tail kinds zig zigZig zigZag)
      {firstSelections secondSelections : List (List (External n))}
      (rest : BothPhaseSelections snapshot key tailTranscript
        firstSelections secondSelections) :
      BothPhaseSelections snapshot key
        (.zigZag step orientation tail tailTranscript)
        firstSelections secondSelections

set_option maxHeartbeats 400000 in
/--
Choose the two phases jointly and pull both endpoint batches back to the
single tree before the complete splay.
-/
theorem exists_bothPhaseSelections_supported
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections,
      BothPhaseSelections snapshot key transcript
          firstSelections secondSelections ∧
      List.Forall₂ (HeapChildrenSupportedIn snapshot before upper_le_n)
        transcript.hitGroups firstSelections ∧
      List.Forall₂ (HeapChildrenSupportedIn snapshot before upper_le_n)
        transcript.hitGroups secondSelections := by
  induction transcript with
  | done root =>
      exact ⟨[], [], .done root,
        by simp [hitGroups, zigZigHitGroups],
        by simp [hitGroups, zigZigHitGroups]⟩
  | @zig lower upper before middle after kinds zig zigZig zigZag
      step tail tailTranscript ih =>
      have kindsNil :=
        tailTranscript.kinds_eq_nil_of_hasRoot_before step.hasRoot_after
      obtain ⟨firstSelections, secondSelections, joint, firstAligned,
        secondAligned⟩ := ih upper_le_n
      subst kinds
      have tailGroupsEmpty : tailTranscript.hitGroups = [] := by
        simp [hitGroups, zigZigHitGroups]
      rw [tailGroupsEmpty] at firstAligned secondAligned
      cases firstAligned
      cases secondAligned
      exact ⟨[], [], .zig step tail tailTranscript joint,
        by simp [hitGroups, zigZigHitGroups],
        by simp [hitGroups, zigZigHitGroups]⟩
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript ih =>
      obtain ⟨firstSelections, secondSelections, joint, firstAligned,
        secondAligned⟩ := ih upper_le_n
      have supportAncestors :
          ∀ support ∈ tailTranscript.hitGroups, ∀ attachment ∈ support,
            attachment ∈ (middle.searchPath key).dropLast.reverse := by
        intro support supportMember attachment attachmentMember
        apply tailTranscript.flatten_hitGroups_sublist_hitNodes.mem
        simp only [hitGroups, SplayExecution.hitNodes]
        exact List.mem_flatten.mpr
          ⟨support, supportMember, attachmentMember⟩
      have firstBefore := HeapChildrenSupportedIn.pullback_double
        step upper_le_n supportAncestors firstAligned
      have secondBefore := HeapChildrenSupportedIn.pullback_double
        step upper_le_n supportAncestors secondAligned
      obtain ⟨winner, firstLoser, secondLoser, endpoints⟩ :=
        ZigZigBothPairingEndpointsAt.exists_of_orientation
          snapshot orientation upper_le_n
      have firstHead := endpoints.first.heapChildren_supportedIn_take
        step upper_le_n key_lt_n rankZero
      have secondHead := endpoints.second.heapChildren_supportedIn_take
        step upper_le_n key_lt_n rankZero
      refine ⟨[winner, firstLoser] :: firstSelections,
        [winner, secondLoser] :: secondSelections,
        .zigZig step orientation tail tailTranscript endpoints joint, ?_, ?_⟩
      · apply List.Forall₂.cons firstHead
        simpa only [hitGroups, SplayExecution.hitNodes, zigZigHitGroups,
          SplayExecution.drop_two_hitNodes_of_double step] using firstBefore
      · apply List.Forall₂.cons secondHead
        simpa only [hitGroups, SplayExecution.hitNodes, zigZigHitGroups,
          SplayExecution.drop_two_hitNodes_of_double step] using secondBefore
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript ih =>
      obtain ⟨firstSelections, secondSelections, joint, firstAligned,
        secondAligned⟩ := ih upper_le_n
      have supportAncestors :
          ∀ support ∈ tailTranscript.hitGroups, ∀ attachment ∈ support,
            attachment ∈ (middle.searchPath key).dropLast.reverse := by
        intro support supportMember attachment attachmentMember
        apply tailTranscript.flatten_hitGroups_sublist_hitNodes.mem
        simp only [hitGroups, SplayExecution.hitNodes]
        exact List.mem_flatten.mpr
          ⟨support, supportMember, attachmentMember⟩
      have firstBefore := HeapChildrenSupportedIn.pullback_double
        step upper_le_n supportAncestors firstAligned
      have secondBefore := HeapChildrenSupportedIn.pullback_double
        step upper_le_n supportAncestors secondAligned
      refine ⟨firstSelections, secondSelections,
        .zigZag step orientation tail tailTranscript joint, ?_, ?_⟩
      · simpa only [hitGroups, SplayExecution.hitNodes, zigZigHitGroups,
          SplayExecution.drop_two_hitNodes_of_double step] using firstBefore
      · simpa only [hitGroups, SplayExecution.hitNodes, zigZigHitGroups,
          SplayExecution.drop_two_hitNodes_of_double step] using secondBefore

/--
The joint schedule aligned with the global four-child indices.  Each phase
is duplicate-free, while the joint witness retains the sequential relation
between the two lists.
-/
theorem exists_bothPhaseSelections_atDoubleGroups
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    ∃ firstSelections secondSelections,
      BothPhaseSelections snapshot key transcript
          firstSelections secondSelections ∧
        List.Forall₂
          (PhaseSelectionSupportedAtDoubleGroup
            snapshot before upper_le_n execution)
          (zigZigDoubleGroupIndices kinds 0) firstSelections ∧
        List.Forall₂
          (PhaseSelectionSupportedAtDoubleGroup
            snapshot before upper_le_n execution)
          (zigZigDoubleGroupIndices kinds 0) secondSelections ∧
        firstSelections.flatten.Nodup ∧
        secondSelections.flatten.Nodup := by
  obtain ⟨firstSelections, secondSelections, joint, firstSupported,
      secondSupported⟩ :=
    transcript.exists_bothPhaseSelections_supported
      upper_le_n key_lt_n rankZero
  have indexed :
      List.Forall₂
        (fun group support =>
          support = (execution.hitNodes.drop (2 * group)).take 2)
        (zigZigDoubleGroupIndices kinds 0) transcript.hitGroups := by
    simpa [SplayExecutionTranscript.hitGroups] using
      transcript.hitSideSchedule
        |>.forall₂_doubleGroupIndices_zigZigHitGroups execution.hitNodes 0
  have firstNodup : firstSelections.flatten.Nodup :=
    HeapChildrenSupportedIn.flatten_nodup
      transcript.flatten_zigZigHitGroups_nodup firstSupported
  have secondNodup : secondSelections.flatten.Nodup :=
    HeapChildrenSupportedIn.flatten_nodup
      transcript.flatten_zigZigHitGroups_nodup secondSupported
  exact ⟨firstSelections, secondSelections, joint,
    forall₂_phaseSelectionSupportedAtDoubleGroup indexed firstSupported,
    forall₂_phaseSelectionSupportedAtDoubleGroup indexed secondSupported,
    firstNodup, secondNodup⟩

end SplayExecutionTranscript

/--
One joint selection records the exact two-step local adjacency claimed in
the zig-zig-to-pairings lemma.
-/
def SequentialPhaseSelection {n : ℕ}
    (first second : List (External n)) : Prop :=
  ∃ winner firstLoser secondLoser candidates,
    first = [winner, firstLoser] ∧
      second = [winner, secondLoser] ∧
      Interface.Adjacent candidates winner firstLoser ∧
      Interface.Adjacent (candidates.erase firstLoser) winner secondLoser ∧
      firstLoser ≠ secondLoser ∧
      candidates.Perm [winner, firstLoser, secondLoser]

/--
The position-aware version of `SequentialPhaseSelection`.  Besides the two
selected endpoint pairs, it records the exact four-child group in the
initial bottom-up root-heavy-path order.  This is the alignment needed when
the article later retains only the groups fully contained in one lazy
interval.
-/
def SequentialPhaseSelectionAtDoubleGroup
    {n lower upper : ℕ} (snapshot : Snapshot n)
    (before : BST lower upper) (upper_le_n : upper ≤ n)
    (key group : ℕ)
    (selections : List (External n) × List (External n)) : Prop :=
  ∃ extra winner firstLoser secondLoser candidates,
    selections.1 = [winner, firstLoser] ∧
      selections.2 = [winner, secondLoser] ∧
      ((rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0).drop
        (4 * group)).take 4 = extra :: candidates ∧
      candidates.length = 3 ∧
      Interface.Adjacent candidates winner firstLoser ∧
      Interface.Adjacent (candidates.erase firstLoser)
        winner secondLoser ∧
      firstLoser ≠ secondLoser ∧
      candidates.Perm [winner, firstLoser, secondLoser] ∧
      snapshot.rank winner < snapshot.rank firstLoser ∧
      snapshot.rank winner < snapshot.rank secondLoser

/-- Raising the starting double-group index raises every selected zig-zig
index by one. -/
theorem zigZigDoubleGroupIndices_succ
    (kinds : List SplayStepKind) (start : ℕ) :
    zigZigDoubleGroupIndices kinds (start + 1) =
      (zigZigDoubleGroupIndices kinds start).map Nat.succ := by
  induction kinds generalizing start with
  | nil => simp [zigZigDoubleGroupIndices]
  | cons kind kinds ih =>
      cases kind with
      | zig => simpa [zigZigDoubleGroupIndices] using ih start
      | zigZig =>
          simp only [zigZigDoubleGroupIndices, List.map_cons]
          apply congrArg₂ List.cons
          · omega
          · simpa [Nat.add_assoc] using ih (start + 1)
      | zigZag =>
          simpa [zigZigDoubleGroupIndices, Nat.add_assoc] using ih (start + 1)

/-- Every emitted global double-group index is at least the starting index. -/
theorem le_of_mem_zigZigDoubleGroupIndices
    {kinds : List SplayStepKind} {start group : ℕ}
    (member : group ∈ zigZigDoubleGroupIndices kinds start) :
    start ≤ group := by
  induction kinds generalizing start with
  | nil => simp [zigZigDoubleGroupIndices] at member
  | cons kind kinds ih =>
      cases kind with
      | zig => exact ih member
      | zigZig =>
          simp only [zigZigDoubleGroupIndices, List.mem_cons] at member
          rcases member with rfl | tailMember
          · exact Nat.le_refl _
          · exact Nat.le_trans (Nat.le_succ start) (ih tailMember)
      | zigZag =>
          exact Nat.le_trans (Nat.le_succ start) (ih member)

/-- Global zig-zig group indices occur without repetition. -/
theorem zigZigDoubleGroupIndices_nodup
    (kinds : List SplayStepKind) (start : ℕ) :
    (zigZigDoubleGroupIndices kinds start).Nodup := by
  induction kinds generalizing start with
  | nil => simp [zigZigDoubleGroupIndices]
  | cons kind kinds ih =>
      cases kind with
      | zig => simpa [zigZigDoubleGroupIndices] using ih start
      | zigZig =>
          rw [zigZigDoubleGroupIndices]
          apply List.nodup_cons.mpr
          constructor
          · intro member
            have lower := le_of_mem_zigZigDoubleGroupIndices member
            omega
          · exact ih (start + 1)
      | zigZag =>
          simpa [zigZigDoubleGroupIndices] using ih (start + 1)

private theorem drop_four_chunk
    {alpha : Type*} {chunk before after : List alpha} (group : ℕ)
    (chunkLength : chunk.length = 4)
    (decomposition : before = chunk ++ after) :
    (before.drop (4 * (group + 1))).take 4 =
      (after.drop (4 * group)).take 4 := by
  rw [decomposition, List.drop_append]
  have dropChunk : chunk.drop (4 * (group + 1)) = [] := by
    apply List.drop_eq_nil_iff.mpr
    omega
  rw [dropChunk]
  simp only [List.nil_append]
  congr 2
  omega

namespace SplayExecutionTranscript.BothPhaseSelections

/-- Every paired entry of the joint transcript has sequential adjacency. -/
theorem forall₂_sequential
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {firstSelections secondSelections : List (List (External n))}
    (joint : BothPhaseSelections snapshot key transcript
      firstSelections secondSelections) :
    List.Forall₂ SequentialPhaseSelection
      firstSelections secondSelections := by
  induction joint with
  | done root => exact .nil
  | zig step tail tailTranscript rest ih => exact ih
  | zigZig step orientation tail tailTranscript endpoints rest ih =>
      obtain ⟨candidates, firstAdjacent, secondAdjacent, candidatePerm⟩ :=
        endpoints.sequential_adjacency
      apply List.Forall₂.cons
      · exact ⟨_, _, _, candidates, rfl, rfl, firstAdjacent,
          secondAdjacent, endpoints.losers_ne, candidatePerm⟩
      · exact ih
  | zigZag step orientation tail tailTranscript rest ih => exact ih

/--
The local three-candidate run of every selected zig-zig is exactly positions
one through three of its global four-child group in the initial bottom-up
root-heavy-path order.  Earlier double steps merely remove four-child
prefixes, so no order information is lost when moving back to the initial
tree.
-/
theorem exists_sequential_atDoubleGroup
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {firstSelections secondSelections : List (List (External n))}
    (joint : BothPhaseSelections snapshot key transcript
      firstSelections secondSelections)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0)
    {group : ℕ} (groupMember : group ∈ zigZigDoubleGroupIndices kinds 0) :
    ∃ firstSelection secondSelection extra winner firstLoser secondLoser
        candidates,
      firstSelection ∈ firstSelections ∧
        secondSelection ∈ secondSelections ∧
        firstSelection = [winner, firstLoser] ∧
        secondSelection = [winner, secondLoser] ∧
        ((rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0).drop
          (4 * group)).take 4 = extra :: candidates ∧
        candidates.length = 3 ∧
        Interface.Adjacent candidates winner firstLoser ∧
        Interface.Adjacent (candidates.erase firstLoser)
          winner secondLoser ∧
        firstLoser ≠ secondLoser ∧
        candidates.Perm [winner, firstLoser, secondLoser] := by
  induction joint generalizing group with
  | done root => simp [zigZigDoubleGroupIndices] at groupMember
  | @zig lower upper before middle after kinds zig zigZig zigZag step tail
      tailTranscript firstSelections secondSelections rest ih =>
      have kindsNil :=
        tailTranscript.kinds_eq_nil_of_hasRoot_before step.hasRoot_after
      subst kinds
      simp [zigZigDoubleGroupIndices] at groupMember
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript winner firstLoser secondLoser
      endpoints firstSelections secondSelections rest ih =>
      simp only [zigZigDoubleGroupIndices, List.mem_cons] at groupMember
      rcases groupMember with rfl | tailMember
      · obtain ⟨extra, candidates, suffix, wholeEq, candidateLength,
            firstAdjacent, secondAdjacent, candidatePerm⟩ :=
          endpoints.sequential_geometry_at_rootHeavyPath_prefix
            upper_le_n key_lt_n rankZero 0
        have prefixLength : (extra :: candidates).length = 4 := by
          simp [candidateLength]
        have chunkEq :
            (rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0).take
                4 = extra :: candidates := by
          rw [wholeEq]
          rw [List.take_append_of_le_length (show
            4 ≤ (extra :: candidates).length by omega)]
          exact (List.take_eq_self_iff (extra :: candidates)).2 (by omega)
        exact ⟨[winner, firstLoser], [winner, secondLoser], extra, winner,
          firstLoser, secondLoser, candidates, by simp, by simp, rfl, rfl,
          by simpa using chunkEq, candidateLength, firstAdjacent,
          secondAdjacent, endpoints.losers_ne, candidatePerm⟩
      · rw [zigZigDoubleGroupIndices_succ kinds 0] at tailMember
        obtain ⟨localGroup, localMember, groupEq⟩ :=
          List.mem_map.mp tailMember
        subst group
        obtain ⟨firstSelection, secondSelection, extra, selectedWinner,
            selectedFirstLoser, selectedSecondLoser, candidates, firstMember,
            secondMember, firstEq, secondEq, localChunkEq, candidateLength,
            firstAdjacent, secondAdjacent, losersNe, candidatePerm⟩ :=
          ih upper_le_n localMember
        obtain ⟨chunk, chunkLength, decomposition⟩ :=
          Splay.Accounting.DoubleRotationAt.rootHeavyPathChildrenBottomUp_decompose
            snapshot step upper_le_n key_lt_n rankZero 0
        have shifted := drop_four_chunk localGroup chunkLength decomposition
        refine ⟨firstSelection, secondSelection, extra, selectedWinner,
          selectedFirstLoser, selectedSecondLoser, candidates,
          by simp [firstMember], by simp [secondMember], firstEq, secondEq,
          ?_, candidateLength, firstAdjacent, secondAdjacent, losersNe,
          candidatePerm⟩
        rw [shifted]
        exact localChunkEq
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript firstSelections secondSelections
      rest ih =>
      simp only [zigZigDoubleGroupIndices] at groupMember
      rw [zigZigDoubleGroupIndices_succ kinds 0] at groupMember
      obtain ⟨localGroup, localMember, groupEq⟩ :=
        List.mem_map.mp groupMember
      subst group
      obtain ⟨firstSelection, secondSelection, extra, selectedWinner,
          selectedFirstLoser, selectedSecondLoser, candidates, firstMember,
          secondMember, firstEq, secondEq, localChunkEq, candidateLength,
          firstAdjacent, secondAdjacent, losersNe, candidatePerm⟩ :=
        ih upper_le_n localMember
      obtain ⟨chunk, chunkLength, decomposition⟩ :=
        Splay.Accounting.DoubleRotationAt.rootHeavyPathChildrenBottomUp_decompose
          snapshot step upper_le_n key_lt_n rankZero 0
      have shifted := drop_four_chunk localGroup chunkLength decomposition
      refine ⟨firstSelection, secondSelection, extra, selectedWinner,
        selectedFirstLoser, selectedSecondLoser, candidates, firstMember,
        secondMember, firstEq, secondEq, ?_, candidateLength, firstAdjacent,
        secondAdjacent, losersNe, candidatePerm⟩
      rw [shifted]
      exact localChunkEq

private theorem sequentialPhaseSelectionAtDoubleGroup_succ
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before middle : BST lower upper}
    (upper_le_n : upper ≤ n)
    {chunk : List (External n)}
    (chunkLength : chunk.length = 4)
    (decomposition :
      rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0 =
        chunk ++
          rootHeavyPathChildrenBottomUp snapshot middle upper_le_n key 0)
    {group : ℕ} {selections : List (External n) × List (External n)}
    (selected : SequentialPhaseSelectionAtDoubleGroup
      snapshot middle upper_le_n key group selections) :
    SequentialPhaseSelectionAtDoubleGroup
      snapshot before upper_le_n key (group + 1) selections := by
  obtain ⟨extra, winner, firstLoser, secondLoser, candidates,
      firstEq, secondEq, localChunkEq, candidateLength, firstAdjacent,
      secondAdjacent, losersNe, candidatePerm, firstRankLt,
      secondRankLt⟩ := selected
  refine ⟨extra, winner, firstLoser, secondLoser, candidates,
    firstEq, secondEq, ?_, candidateLength, firstAdjacent,
    secondAdjacent, losersNe, candidatePerm, firstRankLt, secondRankLt⟩
  rw [drop_four_chunk group chunkLength decomposition]
  exact localChunkEq

private theorem forall₂_sequentialPhaseSelectionAtDoubleGroup_succ
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before middle : BST lower upper}
    (upper_le_n : upper ≤ n)
    {chunk : List (External n)}
    (chunkLength : chunk.length = 4)
    (decomposition :
      rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0 =
        chunk ++
          rootHeavyPathChildrenBottomUp snapshot middle upper_le_n key 0)
    {groups : List ℕ}
    {selections : List (List (External n) × List (External n))}
    (selected : List.Forall₂
      (SequentialPhaseSelectionAtDoubleGroup snapshot middle upper_le_n key)
      groups selections) :
    List.Forall₂
      (SequentialPhaseSelectionAtDoubleGroup snapshot before upper_le_n key)
      (groups.map Nat.succ) selections := by
  induction selected with
  | nil => exact .nil
  | @cons group selection groups selections head tail ih =>
      apply List.Forall₂.cons
      · simpa only [Nat.succ_eq_add_one] using
          sequentialPhaseSelectionAtDoubleGroup_succ upper_le_n
            chunkLength decomposition head
      · exact ih

/--
All joint selections are aligned, in one `Forall₂`, with their exact global
four-child groups.  In particular, filtering this alignment retains the
same row in the first and second article phases; no choice-by-membership can
accidentally duplicate or reorder a pairing.
-/
theorem forall₂_sequential_atDoubleGroups
    {n key lower upper : ℕ} {snapshot : Snapshot n}
    {before after : BST lower upper}
    {execution : SplayExecution key before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplayExecutionTranscript key execution kinds zig zigZig zigZag}
    {firstSelections secondSelections : List (List (External n))}
    (joint : BothPhaseSelections snapshot key transcript
      firstSelections secondSelections)
    (upper_le_n : upper ≤ n) (key_lt_n : key < n)
    (rankZero : snapshot.rank (valuePos ⟨key, key_lt_n⟩) = 0) :
    List.Forall₂
      (SequentialPhaseSelectionAtDoubleGroup snapshot before upper_le_n key)
      (zigZigDoubleGroupIndices kinds 0)
      (firstSelections.zip secondSelections) := by
  induction joint with
  | done root => exact .nil
  | @zig lower upper before middle after kinds zig zigZig zigZag step tail
      tailTranscript firstSelections secondSelections rest ih =>
      have kindsNil :=
        tailTranscript.kinds_eq_nil_of_hasRoot_before step.hasRoot_after
      subst kinds
      simp only [zigZigDoubleGroupIndices] at ih ⊢
      have empty := ih upper_le_n
      have zipLength : (firstSelections.zip secondSelections).length = 0 := by
        simpa using empty.length_eq.symm
      have zipNil : firstSelections.zip secondSelections = [] :=
        List.length_eq_zero_iff.mp zipLength
      rw [zipNil]
      exact .nil
  | @zigZig depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript winner firstLoser secondLoser
      endpoints firstSelections secondSelections rest ih =>
      obtain ⟨extra, candidates, suffix, wholeEq, candidateLength,
          firstAdjacent, secondAdjacent, candidatePerm⟩ :=
        endpoints.sequential_geometry_at_rootHeavyPath_prefix
          upper_le_n key_lt_n rankZero 0
      have chunkEq :
          (rootHeavyPathChildrenBottomUp snapshot before upper_le_n key 0).take
              4 = extra :: candidates := by
        rw [wholeEq]
        rw [List.take_append_of_le_length (show
          4 ≤ (extra :: candidates).length by simp [candidateLength])]
        exact (List.take_eq_self_iff (extra :: candidates)).2
          (by simp [candidateLength])
      have head : SequentialPhaseSelectionAtDoubleGroup
          snapshot before upper_le_n key 0
          ([winner, firstLoser], [winner, secondLoser]) :=
        ⟨extra, winner, firstLoser, secondLoser, candidates,
          rfl, rfl, by simpa using chunkEq, candidateLength,
          firstAdjacent, secondAdjacent, endpoints.losers_ne,
          candidatePerm, endpoints.first.rank_lt, endpoints.second.rank_lt⟩
      obtain ⟨chunk, chunkLength, decomposition⟩ :=
        Splay.Accounting.DoubleRotationAt.rootHeavyPathChildrenBottomUp_decompose
          snapshot step upper_le_n key_lt_n rankZero 0
      have shifted :=
        forall₂_sequentialPhaseSelectionAtDoubleGroup_succ upper_le_n
          chunkLength decomposition (ih upper_le_n)
      simp only [zigZigDoubleGroupIndices, List.zip_cons_cons]
      apply List.Forall₂.cons head
      rw [zigZigDoubleGroupIndices_succ kinds 0]
      exact shifted
  | @zigZag depth lower upper before middle after kinds zig zigZig zigZag
      step orientation tail tailTranscript firstSelections secondSelections
      rest ih =>
      obtain ⟨chunk, chunkLength, decomposition⟩ :=
        Splay.Accounting.DoubleRotationAt.rootHeavyPathChildrenBottomUp_decompose
          snapshot step upper_le_n key_lt_n rankZero 0
      have shifted :=
        forall₂_sequentialPhaseSelectionAtDoubleGroup_succ upper_le_n
          chunkLength decomposition (ih upper_le_n)
      simpa only [zigZigDoubleGroupIndices,
        zigZigDoubleGroupIndices_succ] using shifted

end SplayExecutionTranscript.BothPhaseSelections

/-- Lockstep lookup through two group alignments and their joint phase relation. -/
theorem exists_joint_of_mem_forall₂
    {α β γ : Type*} {left : List α} {middle : List β} {right : List γ}
    {leftMiddle : α → β → Prop} {leftRight : α → γ → Prop}
    {middleRight : β → γ → Prop}
    (firstAligned : List.Forall₂ leftMiddle left middle)
    (secondAligned : List.Forall₂ leftRight left right)
    (joint : List.Forall₂ middleRight middle right)
    {item : α} (member : item ∈ left) :
    ∃ middleItem rightItem,
      middleItem ∈ middle ∧ rightItem ∈ right ∧
        leftMiddle item middleItem ∧ leftRight item rightItem ∧
        middleRight middleItem rightItem := by
  induction firstAligned generalizing right with
  | nil => simp at member
  | @cons first middleItem left middle firstRelated firstRest ih =>
      cases secondAligned with
      | cons secondRelated secondRest =>
          cases joint with
          | cons jointRelated jointRest =>
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · exact ⟨middleItem, _, by simp, by simp,
                  firstRelated, secondRelated, jointRelated⟩
              · obtain ⟨selectedMiddle, selectedRight, middleMember,
                  rightMember, firstSelected, secondSelected,
                  jointSelected⟩ := ih secondRest jointRest tailMember
                exact ⟨selectedMiddle, selectedRight,
                  by simp [middleMember], by simp [rightMember],
                  firstSelected, secondSelected, jointSelected⟩

end Splay.Accounting
