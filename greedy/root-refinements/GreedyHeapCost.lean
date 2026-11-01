import GeometricGreedy
import SurfaceTouchPaths
import SurfaceUpdate
import ValueNullRanks
import ComparatorHeapEdges
import Mathlib.Algebra.BigOperators.Intervals

/-!
Exact geometric touch count versus the number of actual canonical heap
root children. Every touched refinement node contributes its two light
edges, with no contribution from untouched nodes.
-/

namespace GreedyMerge.HeapCost

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open Surface ValueNull Geometry
open scoped BigOperators

theorem touchCount_eq_sum {n lo hi access : ℕ} (height : ℕ → ℤ) (tree : BST lo hi) :
    TouchCount height n access tree =
      ∑ key ∈ Finset.Ico lo hi, Indicator (Neighborhood height n key access) := by
  induction tree with
  | empty => simp [TouchCount]
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      rw [← Finset.sum_Ico_consecutive _ hlo (by omega : root ≤ hi),
        Finset.sum_eq_sum_Ico_succ_bot (by omega : root < hi)]
      simp only [TouchCount, ihLeft, ihRight]
      omega

theorem touchCount_eq_card {n access : ℕ} (height : ℕ → ℤ) (tree : BST 0 n) :
    TouchCount height n access tree = (GreedyRow height n access).card := by
  classical
  rw [touchCount_eq_sum]
  simp only [GreedyRow, Finset.card_filter, Indicator, ← Finset.range_eq_Ico]

noncomputable def HeapChildCount {n lo hi : ℕ} (snapshot : Snapshot n)
    (tree : BST lo hi) (hhi : hi ≤ n) (depth : ℕ) (owner : External n) : ℕ :=
  ((treeEdges snapshot tree hhi depth).filter fun edge => decide (edge.owner = owner)).length

theorem local_owner_filter_length {n : ℕ} (snapshot : Snapshot n) (node : AtNode n)
    (depth : ℕ) (record : External n) :
    ((edgesAtNode snapshot node depth).filter fun edge => decide (edge.owner = record)).length =
      if node.owner snapshot = record then 2 else 0 := by
  classical
  by_cases ownerEq : node.owner snapshot = record
  · have all : (edgesAtNode snapshot node depth).filter
        (fun edge => decide (edge.owner = record)) = edgesAtNode snapshot node depth := by
      apply List.filter_eq_self.mpr
      intro edge member
      have valid := mem_edgesAtNode_valid snapshot node depth member
      simp only [decide_eq_true_eq]
      exact valid.2.1.trans ownerEq
    rw [all, length_edgesAtNode, if_pos ownerEq]
  · have none : (edgesAtNode snapshot node depth).filter
        (fun edge => decide (edge.owner = record)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      have valid := mem_edgesAtNode_valid snapshot node depth member
      intro equal
      have equal : edge.owner = record := of_decide_eq_true equal
      exact ownerEq (valid.2.1.symm.trans equal)
    rw [none, List.length_nil, if_neg ownerEq]

theorem childCount_eq_ownerCount {n lo hi access : ℕ}
    (comparator : BST 0 n) (tree : BST lo hi) (hhi : hi ≤ n)
    (owner : ℕ → ℕ) (record : External n) (recordValue : record.val = 2 * access + 1)
    (exactOwners : ExactExternalOwners comparator.externalDepth owner tree) (depth : ℕ) :
    HeapChildCount (Snapshot.ofTree comparator) tree hhi depth record =
      2 * OwnerCount owner access tree := by
  classical
  induction tree generalizing depth with
  | empty => simp [HeapChildCount, treeEdges, OwnerCount]
  | @node lo root hi left right ihLeft ihRight =>
      let node : AtNode n := ⟨lo, root, hi, left, right, hhi⟩
      have hroot : root ≤ n := by have := right.lower_le_upper; omega
      have rootMin := exactOwners.1
      have ownerBound : 2 * owner root + 1 < 2 * n + 1 := by
        have upper := rootMin.2.1
        omega
      let externalOwner : External n := ⟨2 * owner root + 1, ownerBound⟩
      have minSpec : Splay.Rank.IsIntervalMin (Snapshot.ofTree comparator).rank
          node.wholeLower node.wholeUpper externalOwner := by
        refine ⟨rootMin.1, rootMin.2.1, ?_⟩
        intro position hlo hhi
        exact rootMin.2.2 position.val hlo hhi
      have ownerEq : node.owner (Snapshot.ofTree comparator) = externalOwner :=
        ((Snapshot.ofTree comparator).intervalMin_unique node.wholeLower node.wholeUpper
          node.whole_nonempty minSpec).symm
      have same : node.owner (Snapshot.ofTree comparator) = record ↔ owner root = access := by
        rw [ownerEq]
        constructor
        · intro equal
          have values := congrArg Fin.val equal
          dsimp only [externalOwner] at values
          omega
        · intro equal
          apply Fin.ext
          dsimp only [externalOwner]
          omega
      have localCount := local_owner_filter_length (Snapshot.ofTree comparator) node depth record
      simp only [same] at localCount
      have leftCount := ihLeft hroot exactOwners.2.1 (depth + 1)
      have rightCount := ihRight hhi exactOwners.2.2 (depth + 1)
      change ((edgesAtNode (Snapshot.ofTree comparator) node depth ++
        treeEdges (Snapshot.ofTree comparator) left hroot (depth + 1) ++
        treeEdges (Snapshot.ofTree comparator) right hhi (depth + 1)).filter
          fun edge => decide (edge.owner = record)).length = _
      simp only [List.filter_append, List.length_append, localCount]
      change (if owner root = access then 2 else 0) +
        HeapChildCount (Snapshot.ofTree comparator) left hroot (depth + 1) record +
        HeapChildCount (Snapshot.ofTree comparator) right hhi (depth + 1) record = _
      rw [leftCount, rightCount]
      simp only [OwnerCount]
      split_ifs <;> omega

/-- Concrete actual-surface cost identity before the consolidation. -/
theorem root_children_eq_twice_greedy {n access : ℕ}
    (height : ℕ → ℤ) (comparator refinement : BST 0 n) (owner : ℕ → ℕ)
    (owners : Owners height comparator.depth owner n)
    (refines : Refines height comparator.depth owner refinement)
    (global : UniqueGlobalMinimum comparator.depth n access)
    (record : External n) (recordValue : record.val = 2 * access + 1) :
    HeapChildCount (Snapshot.ofTree comparator) refinement (Nat.le_refl n) 0 record =
      2 * (GreedyRow height n access).card := by
  rw [childCount_eq_ownerCount comparator refinement (Nat.le_refl n) owner record recordValue
    (full_refinement_externalOwners height comparator owner refinement owners refines) 0]
  rw [← touchCount_eq_ownerCount height comparator.depth owner refinement owners global (Nat.le_refl n)]
  rw [touchCount_eq_card]

/-- Immediately repeating the same access touches only that key. -/
theorem greedyRow_raise_self {n access : ℕ} (height : ℕ → ℤ) (time : ℤ)
    (accessBound : access < n) (above : ∀ key, key < n → height key < time) :
    GreedyRow (RaiseSurface height n access time) n access = {access} := by
  classical
  have selfTouch := neighborhood_self height accessBound
  have accessHeight : RaiseSurface height n access time access = time := by
    simp only [RaiseSurface, if_pos selfTouch]
  apply Finset.ext
  intro key
  rw [mem_greedyRow, Finset.mem_singleton]
  constructor
  · intro visible
    by_contra different
    have accessLower := visible.2.2 access (by omega) (by omega) (Ne.symm different)
    rw [accessHeight] at accessLower
    have keyUpper : RaiseSurface height n access time key ≤ time := by
      unfold RaiseSurface
      split_ifs
      · exact le_rfl
      · exact le_of_lt (above key visible.1)
    omega
  · intro equal
    subst key
    exact neighborhood_self _ accessBound

/-- The exact root degree after recanonicalizing the raised surface is two. -/
theorem root_children_after_raise {n access : ℕ}
    (height : ℕ → ℤ) (time : ℤ) (comparator refinement : BST 0 n) (owner : ℕ → ℕ)
    (owners : Owners (RaiseSurface height n access time) comparator.depth owner n)
    (refines : Refines (RaiseSurface height n access time) comparator.depth owner refinement)
    (global : UniqueGlobalMinimum comparator.depth n access)
    (above : ∀ key, key < n → height key < time)
    (record : External n) (recordValue : record.val = 2 * access + 1) :
    HeapChildCount (Snapshot.ofTree comparator) refinement (Nat.le_refl n) 0 record = 2 := by
  rw [root_children_eq_twice_greedy (RaiseSurface height n access time) comparator refinement
    owner owners refines global record recordValue, greedyRow_raise_self height time global.1 above]
  simp

end GreedyMerge.HeapCost

#print axioms GreedyMerge.HeapCost.root_children_eq_twice_greedy

#print axioms GreedyMerge.HeapCost.root_children_after_raise
