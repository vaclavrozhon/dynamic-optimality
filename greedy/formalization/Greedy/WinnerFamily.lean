import Greedy.WinnerPhase

/-! One membership ticket occurs in at most one source fragment per access. -/

namespace Greedy.WinnerTickets

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory
open scoped BigOperators

noncomputable def familyWins {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (family joined : ℕ) : ℕ :=
  ∑ piece ∈ CreatorPhase.pieces states source, if piece.2.family = family then part data states source piece.1 piece.2 joined else 0

theorem nonzero_piece {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (family joined : ℕ)
    (nonzero : familyWins data states source family joined ≠ 0) :
    ∃ side block, block ∈ (states source side).shrinking ∧ block.family = family ∧ part data states source side block joined ≠ 0 := by
  obtain ⟨⟨side, block⟩, member, contributes⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  by_cases matching : block.family = family
  · exact ⟨side, block, (CreatorPhase.mem_pieces ..).mp member, matching, by simpa only [if_pos matching] using contributes⟩
  · exact False.elim (contributes (if_neg matching))

theorem membership_piece_unique {n clock next joined : ℕ} (states : HeapSides n)
    (inv : FamilyOrder.Invariant clock next states) (source : External n)
    (firstSide secondSide : Bool) (first second : Frozen)
    (firstMem : first ∈ (states source firstSide).shrinking) (secondMem : second ∈ (states source secondSide).shrinking)
    (family : first.family = second.family) (firstJoin : joined ∈ joins first) (secondJoin : joined ∈ joins second) :
    (firstSide, first) = (secondSide, second) := by
  have same := inv.membership_block_unique source source firstSide secondSide first second firstMem secondMem family joined firstJoin secondJoin
  subst second
  have slots := inv.ids.locations (encode n (source, firstSide)) (encode n (source, secondSide)) first.id
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨first, firstMem, rfl⟩))
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨first, secondMem, rfl⟩))
  exact Prod.ext (congrArg Prod.snd ((encode n).injective slots)) rfl

theorem family_eq_part {n access clock next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (family joined : ℕ)
    (valid : ∀ side, Valid source.val side (states source side)) (inv : FamilyOrder.Invariant clock next states)
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking) (named : block.family = family)
    (nonzero : part data states source side block joined ≠ 0) :
    familyWins data states source family joined = part data states source side block joined := by
  classical
  have contains := part_nonzero_contains data states source side block joined (valid side) member nonzero
  unfold familyWins
  rw [Finset.sum_eq_single (side, block)]
  · simp only [named, if_true]
  · intro other otherMem different
    by_cases matching : other.2.family = family
    · rw [if_pos matching]
      by_contra otherNonzero
      have otherPresent := (CreatorPhase.mem_pieces states source other.1 other.2).mp otherMem
      have otherJoin := part_nonzero_contains data states source other.1 other.2 joined (valid other.1) otherPresent otherNonzero
      exact different (membership_piece_unique states inv source other.1 side other.2 block otherPresent member
        (matching.trans named.symm) otherJoin contains)
    · exact if_neg matching
  · intro absent
    exact False.elim (absent ((CreatorPhase.mem_pieces ..).mpr member))

theorem family_bound {n access clock next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (family joined : ℕ)
    (valid : ∀ side, Valid source.val side (states source side)) (inv : FamilyOrder.Invariant clock next states) :
    familyWins data states source family joined ≤ 4 := by
  by_cases zero : familyWins data states source family joined = 0
  · omega
  · obtain ⟨side, block, member, named, nonzero⟩ := nonzero_piece data states source family joined zero
    rw [family_eq_part data states source family joined valid inv side block member named nonzero]
    have history := (inv.ordered.localOrder (encode n (source, side))).2 block (by simpa [table] using member)
    exact part_bound data states source side block joined (valid side) member history

theorem isolated_family_zero {n access clock next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (family joined : ℕ)
    (valid : ∀ side, Valid source.val side (states source side)) (inv : FamilyOrder.Invariant clock next states)
    (isolated : ClosedFamilies.HeapClosed family (ClosedFamilies.Isolated joined) states) :
    familyWins data states source family joined = 0 := by
  by_contra nonzero
  obtain ⟨side, block, member, named, contributes⟩ := nonzero_piece data states source family joined nonzero
  have history := (inv.ordered.localOrder (encode n (source, side))).2 block (by simpa [table] using member)
  have closed := isolated.frozen (encode n (source, side)) block (by simpa [table] using member) named
  exact contributes (part_zero_of_isolated data states source side block joined (valid side) member history closed)

end Greedy.WinnerTickets
