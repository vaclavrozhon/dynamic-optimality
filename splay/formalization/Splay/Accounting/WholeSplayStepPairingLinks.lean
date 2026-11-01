import Splay.Accounting.WholeSplayHeapLinks
import Splay.Accounting.SplayPairingsInParallel

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

/-- The two phase links belonging to one actual contextual zig-zig. Other
rotations have an empty set. The endpoints are taken from the existing
indexed relation, rather than supplied as additional geometric data. -/
noncomputable def stepPairingLinks {n lower upper : ℕ} (snapshot : Snapshot n)
    (depth key : ℕ) (before after : BST lower upper) : Finset (External n × External n) := by
  classical
  exact Finset.univ.filter fun link => ∃ phase,
    ZigZigPairingEndpointsAt snapshot phase (depth := depth) (key := key) before after link.1 link.2

@[simp]
theorem mem_stepPairingLinks {n lower upper : ℕ} (snapshot : Snapshot n)
    (depth key : ℕ) (before after : BST lower upper) (link : External n × External n) :
    link ∈ stepPairingLinks snapshot depth key before after ↔ ∃ phase,
      ZigZigPairingEndpointsAt snapshot phase (depth := depth) (key := key) before after link.1 link.2 := by
  classical
  simp [stepPairingLinks]

/-- The two phase pairings are exactly the local light links. -/
theorem edgesAtNode_heapLinks_eq_pairings {n : ℕ} (snapshot : Snapshot n) (node : AtNode n) :
    ((edgesAtNode snapshot node 0).map heapLink).toFinset =
      {((HeapChildPairing.ofNode snapshot node .first).winner, (HeapChildPairing.ofNode snapshot node .first).loser),
       ((HeapChildPairing.ofNode snapshot node .second).winner, (HeapChildPairing.ofNode snapshot node .second).loser)} := by
  classical
  cases heavy : node.heavyBranch snapshot <;>
    simp [edgesAtNode, lightBranches, allBranches, heapLink, edgeFor,
      HeapChildPairing.ofNode, HeapChildPairing.loserBranch, heavy, Finset.pair_comm]

theorem stepPairingLinks_zigZigLeft {n lower first second third upper : ℕ}
    (snapshot : Snapshot n) (a : BST lower first) (b : BST (first + 1) second)
    (c : BST (second + 1) third) (d : BST (third + 1) upper) (bound : upper ≤ n) :
    stepPairingLinks snapshot 0 first (.node (.node (.node a b) c) d) (.node a (.node b (.node c d))) =
      ((edgesAtNode snapshot ⟨second + 1, third, upper, c, d, bound⟩ 0).map heapLink).toFinset := by
  classical
  rw [edgesAtNode_heapLinks_eq_pairings]
  ext ⟨owner, child⟩
  rw [mem_stepPairingLinks]
  constructor
  · rintro ⟨phase, endpoints⟩
    cases endpoints
    cases phase
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (equal | equal)
    · cases equal
      exact ⟨.first, .zigZigLeft a b c d bound .first⟩
    · cases equal
      exact ⟨.second, .zigZigLeft a b c d bound .second⟩

theorem stepPairingLinks_zigZigRight {n lower first second third upper : ℕ}
    (snapshot : Snapshot n) (a : BST lower first) (b : BST (first + 1) second)
    (c : BST (second + 1) third) (d : BST (third + 1) upper) (bound : upper ≤ n) (secondBound : second ≤ n) :
    stepPairingLinks snapshot 0 third (.node a (.node b (.node c d))) (.node (.node (.node a b) c) d) =
      ((edgesAtNode snapshot ⟨lower, first, second, a, b, secondBound⟩ 0).map heapLink).toFinset := by
  classical
  rw [edgesAtNode_heapLinks_eq_pairings]
  ext ⟨owner, child⟩
  rw [mem_stepPairingLinks]
  constructor
  · rintro ⟨phase, endpoints⟩
    cases endpoints
    cases phase
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (equal | equal)
    · cases equal
      exact ⟨.first, .zigZigRight a b c d bound secondBound .first⟩
    · cases equal
      exact ⟨.second, .zigZigRight a b c d bound secondBound .second⟩

theorem stepPairingLinks_zigZagLeftRight {n lower first second third upper : ℕ}
    (snapshot : Snapshot n) (a : BST lower first) (b : BST (first + 1) second)
    (c : BST (second + 1) third) (d : BST (third + 1) upper) :
    stepPairingLinks snapshot 0 second (.node (.node a (.node b c)) d) (.node (.node a b) (.node c d)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro link member
  obtain ⟨phase, endpoints⟩ := (mem_stepPairingLinks _ _ _ _ _ _).mp member
  cases endpoints

theorem stepPairingLinks_zigZagRightLeft {n lower first second third upper : ℕ}
    (snapshot : Snapshot n) (a : BST lower first) (b : BST (first + 1) second)
    (c : BST (second + 1) third) (d : BST (third + 1) upper) :
    stepPairingLinks snapshot 0 second (.node a (.node (.node b c) d)) (.node (.node a b) (.node c d)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro link member
  obtain ⟨phase, endpoints⟩ := (mem_stepPairingLinks _ _ _ _ _ _).mp member
  cases endpoints

theorem stepPairingLinks_leftContext {n depth key lower root upper : ℕ}
    (snapshot : Snapshot n) (before after : BST lower root) (right : BST (root + 1) upper) (keyBound : key < root) :
    stepPairingLinks snapshot (depth + 1) key (.node before right) (.node after right) =
      stepPairingLinks snapshot depth key before after := by
  ext link
  simp only [mem_stepPairingLinks]
  constructor
  · rintro ⟨phase, endpoints⟩
    cases endpoints with
    | leftContext inside _ => exact ⟨phase, inside⟩
    | rightContext _ inside =>
        have bounds := inside.key_bounds
        omega
  · rintro ⟨phase, endpoints⟩
    exact ⟨phase, .leftContext endpoints right⟩

theorem stepPairingLinks_rightContext {n depth key lower root upper : ℕ}
    (snapshot : Snapshot n) (left : BST lower root) (before after : BST (root + 1) upper)
    (keyBound : root < key) :
    stepPairingLinks snapshot (depth + 1) key (.node left before) (.node left after) =
      stepPairingLinks snapshot depth key before after := by
  ext link
  simp only [mem_stepPairingLinks]
  constructor
  · rintro ⟨phase, endpoints⟩
    cases endpoints with
    | leftContext inside _ =>
        have bounds := inside.key_bounds
        omega
    | rightContext _ inside => exact ⟨phase, inside⟩
  · rintro ⟨phase, endpoints⟩
    exact ⟨phase, .rightContext left endpoints⟩

/-- Endpoint evidence retains the actual zig-zig orientation. -/
theorem ZigZigPairingEndpointsAt.orientation {n depth key lower upper : ℕ}
    {snapshot : Snapshot n} {phase : PairingPhase} {before after : BST lower upper}
    {owner child : External n}
    (endpoints : ZigZigPairingEndpointsAt snapshot phase (depth := depth) (key := key) before after owner child) :
    DoubleOrientationAt true (depth := depth) (key := key) before after := by
  induction endpoints with
  | zigZigLeft a b c d _ _ => exact .zigZigLeft a b c d
  | zigZigRight a b c d _ _ _ => exact .zigZigRight a b c d
  | leftContext _ right ih => exact .leftContext ih right
  | rightContext left _ ih => exact .rightContext left ih

/-- No actual zig-zag has phase links, at any contextual depth. -/
theorem stepPairingLinks_eq_empty_of_zigZag {n depth key lower upper : ℕ}
    (snapshot : Snapshot n) {before after : BST lower upper}
    (orientation : DoubleOrientationAt false (depth := depth) (key := key) before after) :
    stepPairingLinks snapshot depth key before after = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro link member
  obtain ⟨_, endpoints⟩ := (mem_stepPairingLinks _ _ _ _ _ _).mp member
  have impossible := doubleOrientationAt_flag_unique orientation endpoints.orientation
  cases impossible

end Splay.Accounting
