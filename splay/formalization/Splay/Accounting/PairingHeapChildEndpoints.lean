import Splay.Accounting.PairingClassificationGeometry
import Splay.Accounting.RealizedPairingSlotOccurrence

namespace Splay.Accounting

open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy
open Splay.Lazy.Canonical

/-- The two external heavy-path vertices participating in one pairing. -/
structure HeapChildPairing (n : ℕ) where
  winner : Interface.Element n
  loser : Interface.Element n

namespace HeapChildPairing

/--
For the three consecutive heap children exposed by a zig-zig, select the
branch removed in each of the two pairing phases.

The heavy branch contains the overall winner.  If it is an outer branch, the
first pairing removes the adjacent middle branch; if it is the middle branch,
the first pairing removes the right branch.  The second phase removes the
remaining branch.  This is the deterministic version of the manuscript's
"either order" choice when the middle child wins.
-/
def loserBranch :
    TernaryBranch → PairingPhase → TernaryBranch
  | .left, .first => .middle
  | .left, .second => .right
  | .middle, .first => .right
  | .middle, .second => .left
  | .right, .first => .middle
  | .right, .second => .left

/-- The selected loser branch is always light. -/
theorem loserBranch_ne
    (heavy : TernaryBranch) (phase : PairingPhase) :
    loserBranch heavy phase ≠ heavy := by
  cases heavy <;> cases phase <;> decide

/--
The canonical pairing at one of the two phases around an internal node whose
three ternary branches are precisely the three zig-zig candidates.
-/
noncomputable def ofNode {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    (phase : PairingPhase) : HeapChildPairing n where
  winner := node.owner snapshot
  loser :=
    node.branchMin snapshot
      (loserBranch (node.heavyBranch snapshot) phase)

/-- Every selected pairing has strictly increasing comparison rank. -/
theorem ofNode_rank_lt {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    (phase : PairingPhase) :
    snapshot.rank (ofNode snapshot node phase).winner <
      snapshot.rank (ofNode snapshot node phase).loser := by
  exact
    node.owner_rank_lt_branchMin_of_light snapshot
      (loserBranch_ne (node.heavyBranch snapshot) phase)

/-- Winner and loser are distinct external vertices. -/
theorem ofNode_ne {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n)
    (phase : PairingPhase) :
    (ofNode snapshot node phase).winner ≠
      (ofNode snapshot node phase).loser := by
  intro equal
  have rankLt := ofNode_rank_lt snapshot node phase
  rw [equal] at rankLt
  exact Nat.lt_irrefl _ rankLt

/-- The three consecutive heap children relevant to one zig-zig. -/
noncomputable def candidates {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    List (Interface.Element n) :=
  allBranches.map (node.branchMin snapshot)

/-- The manuscript's first pairing uses adjacent candidates. -/
theorem first_adjacent_candidates {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    Interface.Adjacent (candidates snapshot node)
      (ofNode snapshot node .first).winner
      (ofNode snapshot node .first).loser := by
  have ownerEq := node.owner_eq_branchMin_heavy snapshot
  cases heavyEq : node.heavyBranch snapshot with
  | left =>
      refine ⟨[], [node.branchMin snapshot .right], Or.inl ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq]
  | middle =>
      refine ⟨[node.branchMin snapshot .left], [], Or.inl ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq]
  | right =>
      refine ⟨[node.branchMin snapshot .left], [], Or.inr ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq]

/-- Reversing the local order preserves adjacency of the first pairing. -/
theorem first_adjacent_candidates_reverse {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    Interface.Adjacent (candidates snapshot node).reverse
      (ofNode snapshot node .first).winner
      (ofNode snapshot node .first).loser := by
  obtain ⟨front, back, direct | reversed⟩ :=
    first_adjacent_candidates snapshot node
  · refine ⟨back.reverse, front.reverse, Or.inr ?_⟩
    rw [direct, List.reverse_append]
    simp [List.append_assoc]
  · refine ⟨back.reverse, front.reverse, Or.inl ?_⟩
    rw [reversed, List.reverse_append]
    simp [List.append_assoc]

/-- After erasing the first loser, the second pairing becomes adjacent. -/
theorem second_adjacent_after_erase_first {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    Interface.Adjacent
      ((candidates snapshot node).erase
        (ofNode snapshot node .first).loser)
      (ofNode snapshot node .second).winner
      (ofNode snapshot node .second).loser := by
  have ownerEq := node.owner_eq_branchMin_heavy snapshot
  have injective := branchMin_injective snapshot node
  have left_ne_middle :
      node.branchMin snapshot .left ≠ node.branchMin snapshot .middle := by
    intro equal
    exact (show TernaryBranch.left ≠ .middle by decide) (injective equal)
  have left_ne_right :
      node.branchMin snapshot .left ≠ node.branchMin snapshot .right := by
    intro equal
    exact (show TernaryBranch.left ≠ .right by decide) (injective equal)
  have middle_ne_right :
      node.branchMin snapshot .middle ≠ node.branchMin snapshot .right := by
    intro equal
    exact (show TernaryBranch.middle ≠ .right by decide) (injective equal)
  cases heavyEq : node.heavyBranch snapshot with
  | left =>
      refine ⟨[], [], Or.inl ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq,
        left_ne_middle]
  | middle =>
      refine ⟨[], [], Or.inr ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq,
        left_ne_right, middle_ne_right]
  | right =>
      refine ⟨[], [], Or.inr ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq,
        left_ne_middle]

/-- The second phase is also adjacent in the reversed local order. -/
theorem second_adjacent_after_erase_first_reverse {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    Interface.Adjacent
      ((candidates snapshot node).reverse.erase
        (ofNode snapshot node .first).loser)
      (ofNode snapshot node .second).winner
      (ofNode snapshot node .second).loser := by
  have ownerEq := node.owner_eq_branchMin_heavy snapshot
  have injective := branchMin_injective snapshot node
  have middle_ne_right :
      node.branchMin snapshot .middle ≠ node.branchMin snapshot .right := by
    intro equal
    exact (show TernaryBranch.middle ≠ .right by decide) (injective equal)
  have right_ne_middle :
      node.branchMin snapshot .right ≠ node.branchMin snapshot .middle :=
    middle_ne_right.symm
  cases heavyEq : node.heavyBranch snapshot with
  | left =>
      refine ⟨[], [], Or.inr ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq,
        right_ne_middle]
  | middle =>
      refine ⟨[], [], Or.inl ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq]
  | right =>
      refine ⟨[], [], Or.inl ?_⟩
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq,
        right_ne_middle]

/-- The candidate triple is exactly the common winner and the two phase losers. -/
theorem candidates_perm_phaseEndpoints {n : ℕ}
    (snapshot : Snapshot n) (node : AtNode n) :
    (candidates snapshot node).Perm
      [(ofNode snapshot node .first).winner,
       (ofNode snapshot node .first).loser,
       (ofNode snapshot node .second).loser] := by
  have ownerEq := node.owner_eq_branchMin_heavy snapshot
  cases heavyEq : node.heavyBranch snapshot with
  | left =>
      simp [candidates, allBranches, ofNode, loserBranch, heavyEq, ownerEq]
  | middle =>
      simp only [candidates, allBranches, List.map_cons, List.map_nil,
        ofNode, loserBranch, heavyEq, ownerEq]
      exact
        (List.Perm.swap (node.branchMin snapshot .middle)
          (node.branchMin snapshot .left)
          [node.branchMin snapshot .right]).trans
        (List.Perm.cons (node.branchMin snapshot .middle)
          (List.Perm.swap (node.branchMin snapshot .right)
            (node.branchMin snapshot .left) []))
  | right =>
      simp only [candidates, allBranches, List.map_cons, List.map_nil,
        ofNode, loserBranch, heavyEq, ownerEq]
      exact
        (List.Perm.swap (node.branchMin snapshot .middle)
          (node.branchMin snapshot .left)
          [node.branchMin snapshot .right]).trans
        (List.perm_middle (l₁ := [node.branchMin snapshot .middle,
          node.branchMin snapshot .left]) (l₂ := []))

end HeapChildPairing

set_option linter.unusedVariables false in
/--
The exact heap-child endpoints selected by one phase of a concrete
same-direction double rotation.

For a right zig-zig, the three candidates are `y⁺`, the value vertex `z`,
and `z⁺`; these are exactly the left, middle, and right branch minima of the
local node `.node c d`.  The left-zig-zig constructor is the mirror image,
using `.node a b`.  Context constructors retain the same endpoints under
arbitrarily many ancestors.
-/
inductive ZigZigPairingEndpointsAt {n : ℕ} (snapshot : Snapshot n) :
    PairingPhase →
      {depth key lower upper : ℕ} →
      BST lower upper → BST lower upper →
      Interface.Element n → Interface.Element n → Prop
  | zigZigLeft
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper)
      (upper_le_n : upper ≤ n)
      (phase : PairingPhase) :
      ZigZigPairingEndpointsAt snapshot phase
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
        } phase).winner
        (HeapChildPairing.ofNode snapshot {
          lower := second + 1
          root := third
          upper := upper
          left := c
          right := d
          upper_le_n := upper_le_n
        } phase).loser
  | zigZigRight
      {lower first second third upper : ℕ}
      (a : BST lower first)
      (b : BST (first + 1) second)
      (c : BST (second + 1) third)
      (d : BST (third + 1) upper)
      (upper_le_n : upper ≤ n)
      (second_le_n : second ≤ n)
      (phase : PairingPhase) :
      ZigZigPairingEndpointsAt snapshot phase
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
        } phase).winner
        (HeapChildPairing.ofNode snapshot {
          lower := lower
          root := first
          upper := second
          left := a
          right := b
          upper_le_n := second_le_n
        } phase).loser
  | leftContext
      {phase : PairingPhase}
      {depth key lower root upper : ℕ}
      {before after : BST lower root}
      {winner loser : Interface.Element n}
      (inside :
        ZigZigPairingEndpointsAt snapshot phase
          (depth := depth) (key := key)
          before after winner loser)
      (right : BST (root + 1) upper) :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth.succ) (key := key)
        (.node before right) (.node after right)
        winner loser
  | rightContext
      {phase : PairingPhase}
      {depth key lower root upper : ℕ}
      (left : BST lower root)
      {before after : BST (root + 1) upper}
      {winner loser : Interface.Element n}
      (inside :
        ZigZigPairingEndpointsAt snapshot phase
          (depth := depth) (key := key)
          before after winner loser) :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth.succ) (key := key)
        (.node left before) (.node left after)
        winner loser

namespace ZigZigPairingEndpointsAt

/-- A true zig-zig orientation determines heap-child endpoints in each phase. -/
theorem exists_of_orientation
    {n : ℕ} (snapshot : Snapshot n)
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    (orientation :
      DoubleOrientationAt true
        (depth := depth) (key := key) before after)
    (upper_le_n : upper ≤ n)
    (phase : PairingPhase) :
    ∃ winner loser,
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth) (key := key)
        before after winner loser := by
  generalize flag_eq : true = flag at orientation
  induction orientation generalizing phase with
  | zigZigLeft a b c d =>
      exact
        ⟨_, _,
          .zigZigLeft a b c d upper_le_n phase⟩
  | zigZigRight a b c d =>
      exact
        ⟨_, _,
          .zigZigRight a b c d upper_le_n (by
            have cBounds := c.lower_le_upper
            have dBounds := d.lower_le_upper
            omega) phase⟩
  | zigZagLeftRight =>
      contradiction
  | zigZagRightLeft =>
      contradiction
  | leftContext orientation right ih =>
      obtain ⟨winner, loser, endpoints⟩ :=
        ih (by
          have rightBounds := right.lower_le_upper
          omega) phase flag_eq
      exact
        ⟨winner, loser, .leftContext endpoints right⟩
  | rightContext left orientation ih =>
      obtain ⟨winner, loser, endpoints⟩ :=
        ih upper_le_n phase flag_eq
      exact
        ⟨winner, loser, .rightContext left endpoints⟩

/-- Endpoint selection always pairs the lower-rank winner with a loser. -/
theorem rank_lt
    {n : ℕ} {snapshot : Snapshot n}
    {phase : PairingPhase}
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    {winner loser : Interface.Element n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth) (key := key)
        before after winner loser) :
    snapshot.rank winner < snapshot.rank loser := by
  induction endpoints with
  | zigZigLeft a b c d upper_le_n phase =>
      exact HeapChildPairing.ofNode_rank_lt _ _ _
  | zigZigRight a b c d upper_le_n second_le_n phase =>
      exact HeapChildPairing.ofNode_rank_lt _ _ _
  | leftContext inside right ih =>
      exact ih
  | rightContext left inside ih =>
      exact ih

/--
The selected loser is connected to the selected winner by an actual
canonical light edge in the post-zig-zig tree.
-/
theorem exists_after_edge
    {n : ℕ} {snapshot : Snapshot n}
    {phase : PairingPhase}
    {depth key lower upper : ℕ}
    {before after : BST lower upper}
    {winner loser : Interface.Element n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth) (key := key)
        before after winner loser)
    (upper_le_n : upper ≤ n)
    (treeDepth : ℕ) :
    ∃ edge : Edge n,
      edge ∈ treeEdges snapshot after upper_le_n treeDepth ∧
        edge.owner = winner ∧ edge.child = loser := by
  induction endpoints generalizing treeDepth with
  | zigZigLeft a b c d storedUpper phase =>
      let node : AtNode n := {
        lower := _ + 1
        root := _
        upper := _
        left := c
        right := d
        upper_le_n := storedUpper
      }
      let loserBranch :=
        HeapChildPairing.loserBranch
          (node.heavyBranch snapshot) phase
      let edge :=
        edgeFor snapshot node (treeDepth + 1 + 1) loserBranch
      have light :
          loserBranch ≠ node.heavyBranch snapshot :=
        HeapChildPairing.loserBranch_ne _ _
      have localMember :
          edge ∈
            edgesAtNode snapshot node (treeDepth + 1 + 1) := by
        simp only [edge, edgesAtNode, List.mem_map,
          mem_lightBranches_iff]
        exact ⟨loserBranch, light, rfl⟩
      refine ⟨edge, ?_, rfl, rfl⟩
      simp only [treeEdges, List.mem_append]
      aesop
  | zigZigRight a b c d storedUpper second_le_n phase =>
      let node : AtNode n := {
        lower := _
        root := _
        upper := _
        left := a
        right := b
        upper_le_n := second_le_n
      }
      let loserBranch :=
        HeapChildPairing.loserBranch
          (node.heavyBranch snapshot) phase
      let edge :=
        edgeFor snapshot node (treeDepth + 1 + 1) loserBranch
      have light :
          loserBranch ≠ node.heavyBranch snapshot :=
        HeapChildPairing.loserBranch_ne _ _
      have localMember :
          edge ∈
            edgesAtNode snapshot node (treeDepth + 1 + 1) := by
        simp only [edge, edgesAtNode, List.mem_map,
          mem_lightBranches_iff]
        exact ⟨loserBranch, light, rfl⟩
      refine ⟨edge, ?_, rfl, rfl⟩
      simp only [treeEdges, List.mem_append]
      aesop
  | @leftContext phase depth key lower root upper
      before after winner loser inside right ih =>
      have child_le_n : root ≤ n := by
        have rightBounds := right.lower_le_upper
        omega
      obtain ⟨edge, edgeMember, ownerEq, childEq⟩ :=
        ih child_le_n (treeDepth + 1)
      refine ⟨edge, ?_, ownerEq, childEq⟩
      simp only [treeEdges, List.mem_append]
      exact Or.inl (Or.inr edgeMember)
  | @rightContext phase depth key lower root upper
      left before after winner loser inside ih =>
      obtain ⟨edge, edgeMember, ownerEq, childEq⟩ :=
        ih upper_le_n (treeDepth + 1)
      refine ⟨edge, ?_, ownerEq, childEq⟩
      simp only [treeEdges, List.mem_append]
      exact Or.inr edgeMember

end ZigZigPairingEndpointsAt

/--
Any canonical light edge in the full edge list is exactly the incoming edge
used by `canonicalParent`.
-/
theorem canonicalParent_eq_some_of_mem_fullEdges
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (edge : Edge n)
    (member : edge ∈ fullEdges snapshot tree) :
    canonicalParent snapshot tree edge.child = some edge.owner := by
  have rankLt :
      snapshot.rank edge.owner < snapshot.rank edge.child := by
    exact
      mem_treeEdges_rank_lt snapshot tree (Nat.le_refl n)
        (by simpa only [fullEdges] using member)
  have notRoot :
      edge.child ≠ canonicalRoot snapshot tree := by
    intro childEq
    rw [childEq, rank_canonicalRoot_eq_zero] at rankLt
    omega
  obtain ⟨incoming, lookup, incomingMember, incomingChild⟩ :=
    exists_incomingEdge?_eq_some_of_ne_root
      snapshot tree notRoot
  obtain ⟨selected, selectedSpec, selectedUnique⟩ :=
    existsUnique_fullEdge_child_of_ne_root
      snapshot tree edge.child notRoot
  have incomingEq :
      incoming = selected :=
    selectedUnique incoming ⟨incomingMember, incomingChild⟩
  have edgeEq :
      edge = selected :=
    selectedUnique edge ⟨member, rfl⟩
  have incoming_eq_edge : incoming = edge :=
    incomingEq.trans edgeEq.symm
  simp [canonicalParent, lookup, incoming_eq_edge]

/--
For a full-tree occurrence, the pairing loser is definitionally a canonical
heap child of the selected winner after the concrete zig-zig.
-/
theorem ZigZigPairingEndpointsAt.after_canonicalParent
    {n : ℕ} {snapshot : Snapshot n}
    {phase : PairingPhase}
    {depth key : ℕ}
    {before after : BST 0 n}
    {winner loser : Interface.Element n}
    (endpoints :
      ZigZigPairingEndpointsAt snapshot phase
        (depth := depth) (key := key)
        before after winner loser) :
    canonicalParent snapshot after loser = some winner := by
  obtain ⟨edge, member, ownerEq, childEq⟩ :=
    endpoints.exists_after_edge (Nat.le_refl n) 0
  have parent :=
    canonicalParent_eq_some_of_mem_fullEdges
      snapshot after edge (by
        simpa only [fullEdges] using member)
  simpa only [ownerEq, childEq] using parent

/--
One transcript slot together with its actual request/rotation occurrence and
the two canonical heap-child endpoints selected for that slot's phase.
-/
structure PairingSlotHeapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (snapshot : Snapshot n)
    (slot : PairingSlot) : Type where
  occurrence : PairingSlotOccurrence transcript slot
  winner : Interface.Element n
  loser : Interface.Element n
  endpoints :
    ZigZigPairingEndpointsAt snapshot slot.phase
      (depth := occurrence.depth) (key := occurrence.access.val)
      occurrence.stepBefore occurrence.stepAfter winner loser

namespace PairingSlotHeapEndpoints

/-- Every genuine first/second slot has canonical heap-child endpoints. -/
theorem exists_of_mem
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    (snapshot : Snapshot n)
    (slot : PairingSlot)
    (member :
      slot ∈ firstPairings kinds ++ secondPairings kinds) :
    Nonempty (PairingSlotHeapEndpoints transcript snapshot slot) := by
  obtain ⟨occurrence⟩ :=
    exists_pairingSlotOccurrence transcript slot member
  obtain ⟨winner, loser, endpoints⟩ :=
    ZigZigPairingEndpointsAt.exists_of_orientation
      snapshot occurrence.orientation (Nat.le_refl n) slot.phase
  exact
    ⟨{
      occurrence := occurrence
      winner := winner
      loser := loser
      endpoints := endpoints
    }⟩

/-- The selected endpoint ranks satisfy the pairing order. -/
theorem rank_lt
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {slot : PairingSlot}
    (endpoints :
      PairingSlotHeapEndpoints transcript snapshot slot) :
    snapshot.rank endpoints.winner < snapshot.rank endpoints.loser :=
  endpoints.endpoints.rank_lt

/-- The loser is an actual canonical heap child of the winner afterwards. -/
theorem after_canonicalParent
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n} {slot : PairingSlot}
    (endpoints :
      PairingSlotHeapEndpoints transcript snapshot slot) :
    canonicalParent snapshot endpoints.occurrence.stepAfter
        endpoints.loser =
      some endpoints.winner :=
  endpoints.endpoints.after_canonicalParent

end PairingSlotHeapEndpoints

/--
The strongest automatic slot occurrence currently available: exact
chronological splay geometry, canonical heap-child endpoints, and the exact
contiguous rich-event segment representing the same zig-zig.
-/
structure RealizedPairingSlotHeapEndpoints
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (slot : PairingSlot) : Type where
  realized : RealizedPairingSlotOccurrence transcript provenance slot
  winner : Interface.Element n
  loser : Interface.Element n
  endpoints :
    ZigZigPairingEndpointsAt snapshot slot.phase
      (depth := realized.occurrence.depth)
      (key := realized.occurrence.access.val)
      realized.occurrence.stepBefore realized.occurrence.stepAfter
      winner loser

namespace RealizedPairingSlotHeapEndpoints

/--
Stepwise transition provenance automatically supplies the realized segment
and the canonical heap-child endpoint map for every pairing slot.
-/
theorem exists_of_mem
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    (transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag)
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (slot : PairingSlot)
    (member :
      slot ∈ firstPairings kinds ++ secondPairings kinds) :
    Nonempty
      (RealizedPairingSlotHeapEndpoints transcript provenance slot) := by
  obtain ⟨realized⟩ :=
    RealizedPairingSlotOccurrence.exists_of_mem
      transcript provenance slot member
  obtain ⟨winner, loser, endpoints⟩ :=
    ZigZigPairingEndpointsAt.exists_of_orientation
      snapshot realized.occurrence.orientation
        (Nat.le_refl n) slot.phase
  exact
    ⟨{
      realized := realized
      winner := winner
      loser := loser
      endpoints := endpoints
    }⟩

/-- The realized endpoint map retains the strict comparison-rank order. -/
theorem rank_lt
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {slot : PairingSlot}
    (endpoints :
      RealizedPairingSlotHeapEndpoints transcript provenance slot) :
    snapshot.rank endpoints.winner < snapshot.rank endpoints.loser :=
  endpoints.endpoints.rank_lt

/--
The realized slot's loser has the selected winner as its canonical parent in
the exact post-zig-zig tree.
-/
theorem after_canonicalParent
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {slot : PairingSlot}
    (endpoints :
      RealizedPairingSlotHeapEndpoints transcript provenance slot) :
    canonicalParent snapshot
        endpoints.realized.occurrence.stepAfter endpoints.loser =
      some endpoints.winner :=
  endpoints.endpoints.after_canonicalParent

end RealizedPairingSlotHeapEndpoints

/--
A boundary move agrees with the canonical heap-child map of its transcript
slot.  This is now a two-equality condition; no tree geometry remains hidden
inside it.
-/
def BoundaryPairingMove.MatchesHeapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n}
    {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {trace : Trace params initial events final}
    (move : BoundaryPairingMove trace)
    (endpoints :
      PairingSlotHeapEndpoints transcript snapshot move.slot) : Prop :=
  move.winner = endpoints.winner ∧ move.loser = endpoints.loser

/--
Once a boundary move is matched to the automatic endpoint map, its recorded
winner has strictly smaller comparison rank than its loser.
-/
theorem BoundaryPairingMove.rank_lt_of_matchesHeapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n}
    {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    {trace : Trace params initial events final}
    (move : BoundaryPairingMove trace)
    (endpoints :
      PairingSlotHeapEndpoints transcript snapshot move.slot)
    (agrees : move.MatchesHeapEndpoints endpoints) :
    snapshot.rank move.winner < snapshot.rank move.loser := by
  rw [agrees.1, agrees.2]
  exact endpoints.rank_lt

/--
An actual pass tuple agrees with the canonical heap-child map of the
transcript slot assigned to it.
-/
def ActivitySlotMatchesHeapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n}
    {operations : List (Interface.Operation n)}
    (slot : Interface.ActivitySlot operations)
    {pairingSlot : PairingSlot}
    (endpoints :
      PairingSlotHeapEndpoints transcript snapshot pairingSlot) : Prop :=
  slot.pairing.winner = endpoints.winner ∧
    slot.pairing.loser = endpoints.loser

/--
Endpoint agreement transfers the comparison-rank order to the actual pass
tuple selected by an activity slot.
-/
theorem activitySlot_rank_lt_of_matchesHeapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {before after : BST 0 n}
    {sequence : SplaySequence accesses before after}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {snapshot : Snapshot n}
    {operations : List (Interface.Operation n)}
    (slot : Interface.ActivitySlot operations)
    {pairingSlot : PairingSlot}
    (endpoints :
      PairingSlotHeapEndpoints transcript snapshot pairingSlot)
    (agrees : ActivitySlotMatchesHeapEndpoints slot endpoints) :
    snapshot.rank slot.pairing.winner <
      snapshot.rank slot.pairing.loser := by
  rw [agrees.1, agrees.2]
  exact endpoints.rank_lt

namespace PassPairingClassification

/--
Every internal charge automatically inherits canonical heap-child endpoints;
only equality with the already selected pass tuple remains semantic.
-/
theorem internalCharge_heapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : Interface.State n}
    {operations : List (Interface.Operation n)}
    (classification :
      PassPairingClassification transcript params
        initial final operations)
    (snapshot : Snapshot n)
    (charge : PairingSlot × Interface.ActivitySlot operations)
    (member : charge ∈ classification.internalCharges) :
    Nonempty
      (PairingSlotHeapEndpoints transcript snapshot charge.1) :=
  PairingSlotHeapEndpoints.exists_of_mem
    transcript snapshot charge.1
      (classification.internalCharge_slot_mem_pairings charge member)

end PassPairingClassification

namespace BoundaryPassPairingClassification

/-- Every important boundary move inherits the canonical endpoint map. -/
theorem importantMove_heapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (snapshot : Snapshot n)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.importantMoves) :
    Nonempty
      (PairingSlotHeapEndpoints transcript snapshot move.slot) :=
  PairingSlotHeapEndpoints.exists_of_mem
    transcript snapshot move.slot
      (classification.importantMove_slot_mem_pairings move member)

/-- Every unimportant boundary move inherits the canonical endpoint map. -/
theorem unimportantMove_heapEndpoints
    {n : ℕ} {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {params : Interface.Parameters}
    {initial final : State n} {events : List (Event n)}
    (classification :
      BoundaryPassPairingClassification transcript params
        initial final events)
    (snapshot : Snapshot n)
    (move : BoundaryPairingMove classification.trace)
    (member : move ∈ classification.unimportantMoves) :
    Nonempty
      (PairingSlotHeapEndpoints transcript snapshot move.slot) :=
  PairingSlotHeapEndpoints.exists_of_mem
    transcript snapshot move.slot
      (classification.unimportantMove_slot_mem_pairings move member)

end BoundaryPassPairingClassification

end Splay.Accounting
