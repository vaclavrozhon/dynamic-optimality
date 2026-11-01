import Greedy.AccessPhaseSum
import Greedy.RunCutCollapse

/-! At most one literal source fragment contributes to a family and time. -/

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau GreedyMerge.FrozenHistory
open scoped BigOperators

noncomputable def pieces {n : ℕ} (states : HeapSides n) (source : External n) : Finset (Bool × Frozen) := by
  classical
  exact (((states source true).shrinking.map (fun block => (true, block))) ++
    ((states source false).shrinking.map (fun block => (false, block)))).toFinset

theorem mem_pieces {n : ℕ} (states : HeapSides n) (source : External n) (side : Bool) (block : Frozen) :
    (side, block) ∈ pieces states source ↔ block ∈ (states source side).shrinking := by
  classical
  cases side <;> simp [pieces]

noncomputable def familyCoefficient {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (creator family time : ℕ) : ℤ :=
  ∑ piece ∈ pieces states source, if piece.2.creator = creator ∧ piece.2.family = family then
    part data states source piece.1 piece.2 time else 0

theorem nonzero_piece {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (creator family time : ℕ)
    (nonzero : familyCoefficient data states source creator family time ≠ 0) :
    ∃ side block, block ∈ (states source side).shrinking ∧ block.creator = creator ∧ block.family = family ∧
      part data states source side block time ≠ 0 := by
  obtain ⟨⟨side, block⟩, member, contributes⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  by_cases matching : block.creator = creator ∧ block.family = family
  · exact ⟨side, block, (mem_pieces ..).mp member, matching.1, matching.2, by simpa only [if_pos matching] using contributes⟩
  · exact False.elim (contributes (if_neg matching))

theorem crossing_piece_unique {n clock next cut : ℕ} (states : HeapSides n)
    (inv : FamilyOrder.Invariant clock next states) (source : External n)
    (firstSide secondSide : Bool) (first second : Frozen)
    (firstMem : first ∈ (states source firstSide).shrinking)
    (secondMem : second ∈ (states source secondSide).shrinking) (family : first.family = second.family)
    (firstCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins first))
    (secondCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins second)) :
    (firstSide, first) = (secondSide, second) := by
  have same := inv.straddling_block_unique source source firstSide secondSide first second
    firstMem secondMem family cut firstCross secondCross
  subst second
  have slots := inv.ids.locations (encode n (source, firstSide)) (encode n (source, secondSide)) first.id
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨first, firstMem, rfl⟩))
    (by simp only [table, Equiv.symm_apply_apply]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨first, secondMem, rfl⟩))
  have sideEq := congrArg Prod.snd ((encode n).injective slots)
  exact Prod.ext sideEq rfl

theorem family_eq_part {n access clock next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (creator family time : ℕ)
    (valid : ∀ side, Valid source.val side (states source side))
    (inv : FamilyOrder.Invariant clock next states)
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking)
    (created : block.creator = creator) (named : block.family = family)
    (nonzero : part data states source side block time ≠ 0) :
    familyCoefficient data states source creator family time = part data states source side block time := by
  classical
  have crossing := part_nonzero_crosses data states source side block time (valid side) member nonzero
  unfold familyCoefficient
  rw [Finset.sum_eq_single (side, block)]
  · simp only [created, named, and_self, if_true]
  · intro other otherMem different
    by_cases matching : other.2.creator = creator ∧ other.2.family = family
    · rw [if_pos matching]
      by_contra otherNonzero
      have otherPresent := (mem_pieces states source other.1 other.2).mp otherMem
      have otherCross := part_nonzero_crosses data states source other.1 other.2 time (valid other.1) otherPresent otherNonzero
      exact different (crossing_piece_unique states inv source other.1 side other.2 block
        otherPresent member (matching.2.trans named.symm) otherCross crossing)
    · exact if_neg matching
  · intro absent
    exact False.elim (absent ((mem_pieces states source side block).mpr member))

theorem prepared_family_bound {n : ℕ} (before : Execution.State n) (request : Fin n) (K : ℤ)
    (decomposition : Decomposition before.refined.tree request.val)
    (data : AccessScheduleData before.comparator before.refined.tree
      (Execution.afterRefinement before request).tree decomposition)
    (valid : before.Valid) (root : before.comparator.HasRoot request.val)
    (inv : FamilyOrder.Invariant before.clock before.next before.blocks) (creator family time : ℕ) :
    |familyCoefficient data (RunJournal.prepared before request) (Execution.source request) creator family time| ≤ 3 := by
  by_cases zero : familyCoefficient data (RunJournal.prepared before request) (Execution.source request) creator family time = 0
  · simp [zero]
  · obtain ⟨side, block, member, created, named, nonzero⟩ :=
      nonzero_piece data (RunJournal.prepared before request) (Execution.source request) creator family time zero
    have prepared := FamilyOrder.convertHeap_invariant before.comparator.externalDepth
      (fun owner _ => decide (owner = Execution.source request)) before.next before.blocks inv
    rw [family_eq_part data (RunJournal.prepared before request) (Execution.source request) creator family time
      ((prepared_ready before request valid).valid _) prepared side block member created named nonzero]
    exact prepared_part_bound before request K decomposition data valid root inv side block member time

end Greedy.CreatorPhase
