import Greedy.NegativeBoundaryGeometry
import Greedy.PositiveBoundary

/-!
# Weighted negative entry differences

`Parents` records the actual parent rank at every active-tree node,
using `-1` at a root. A boundary winner whose parent rank is at least
the source base can pay the negative entry difference by its own label
drop. The remaining positive excess is supported on the exceptional
entrances counted in `NegativeBoundaryGeometry`.
-/

namespace Greedy.NegativeBoundary

open GreedyForest.ActiveTree GreedyForest.Phase Splay.Analysis
open Greedy.NegativeBoundaryGeometry Greedy.SparseEdgeSums
open Greedy.WeightedActiveCut
open scoped BigOperators

def Parents (rank : ℕ → ℕ) (parents : ℕ → ℤ) (parentRank : ℤ) : Sparse → Prop
  | .empty => True
  | .node key left right => parents key = parentRank ∧
      Parents rank parents (rank key) left ∧ Parents rank parents (rank key) right

def parentRanks (rank : ℕ → ℕ) (parentRank : ℤ) : Sparse → ℕ → ℤ
  | .empty, _ => parentRank
  | .node key left right, target =>
      if target = key then parentRank else
        if target < key then parentRanks rank (rank key) left target
        else parentRanks rank (rank key) right target

theorem Parents.congr (rank : ℕ → ℕ) (first second : ℕ → ℤ) (tree : Sparse) (parentRank : ℤ)
    (consistent : Parents rank first parentRank tree)
    (equal : ∀ key ∈ tree.keys, first key = second key) : Parents rank second parentRank tree := by
  induction tree generalizing parentRank with
  | empty => trivial
  | node key left right il ir =>
      refine ⟨(equal key (Sparse.root_mem _ _ _)).symm.trans consistent.1, ?_, ?_⟩
      · exact il (rank key) consistent.2.1 (fun v member => equal v (by simp [Sparse.keys, member]))
      · exact ir (rank key) consistent.2.2 (fun v member => equal v (by simp [Sparse.keys, member]))

theorem parentRanks_correct (rank : ℕ → ℕ) (tree : Sparse) (ordered : tree.Ordered) (parentRank : ℤ) :
    Parents rank (parentRanks rank parentRank tree) parentRank tree := by
  induction tree generalizing parentRank with
  | empty => trivial
  | node key left right il ir =>
      refine ⟨by simp [parentRanks], ?_, ?_⟩
      · apply Parents.congr rank _ _ left (rank key) (il ordered.1 (rank key))
        intro v member
        have lt := ordered.2.2.1 v member
        simp [parentRanks, lt, Nat.ne_of_lt lt]
      · apply Parents.congr rank _ _ right (rank key) (ir ordered.2.1 (rank key))
        intro v member
        have lt := ordered.2.2.2 v member
        have different : v ≠ key := by omega
        have notLeft : ¬ v < key := by omega
        simp [parentRanks, different, notLeft]

theorem Parents.edge (rank : ℕ → ℕ) (parents : ℕ → ℤ) (tree : Sparse) (parentRank : ℤ)
    (consistent : Parents rank parents parentRank tree) (edge : ℕ × ℕ) (member : edge ∈ tree.edges) :
    parents edge.2 = (rank edge.1 : ℤ) := by
  induction tree generalizing parentRank with
  | empty => simp [Sparse.edges] at member
  | node root left right il ir =>
      simp only [Sparse.edges, Finset.mem_union] at member
      rcases member with ((hl | hr) | hl) | hr
      · exact il (rank root) consistent.2.1 hl
      · exact ir (rank root) consistent.2.2 hr
      · cases left with
        | empty => simp [Sparse.edgeTo] at hl
        | node key l r =>
            have eq : edge = (root, key) := by simpa [Sparse.edgeTo] using hl
            simpa only [eq] using consistent.2.1.1
      · cases right with
        | empty => simp [Sparse.edgeTo] at hr
        | node key l r =>
            have eq : edge = (root, key) := by simpa [Sparse.edgeTo] using hr
            simpa only [eq] using consistent.2.2.1

def Incoming (first finish : ℕ) (edge : ℕ × ℕ) : Prop :=
  ¬ Inside first finish edge.1 ∧ Inside first finish edge.2

instance (first finish : ℕ) (edge : ℕ × ℕ) : Decidable (Incoming first finish edge) :=
  inferInstanceAs (Decidable (_ ∧ _))

def winnerDrop (rank : ℕ → ℕ) (labels parents : ℕ → ℤ) (key : ℕ) : ℤ :=
  if parents key < 0 then 0 else
    max 0 (labels key - (contractedGap (rank key - (parents key).toNat) : ℤ))

def excess (rank : ℕ → ℕ) (labels parents : ℕ → ℤ) (first finish : ℕ) (edge : ℕ × ℕ) : ℤ :=
  if Incoming first finish edge then
    max 0 (max 0 (labels edge.1 - labels edge.2) - winnerDrop rank labels parents edge.1)
  else 0

theorem winnerDrop_nonneg (rank : ℕ → ℕ) (labels parents : ℕ → ℤ) (key : ℕ) :
    0 ≤ winnerDrop rank labels parents key := by
  unfold winnerDrop
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem safe_drop (rank : ℕ → ℕ) (labels parents : ℕ → ℤ) (base : ℕ) (edge : ℕ × ℕ)
    (floor : (base : ℤ) ≤ parents edge.1) (order : rank edge.1 ≤ rank edge.2)
    (source : labels edge.2 = baseLabel rank base edge.2) :
    max 0 (labels edge.1 - labels edge.2) ≤ winnerDrop rank labels parents edge.1 := by
  have nonneg : 0 ≤ parents edge.1 := by omega
  have natFloor : base ≤ (parents edge.1).toNat := by omega
  have gap := contractedGap_mono
    (show rank edge.1 - (parents edge.1).toNat ≤ rank edge.2 - base by omega)
  have bound : (contractedGap (rank edge.1 - (parents edge.1).toNat) : ℤ) ≤ labels edge.2 := by
    rw [source]
    unfold baseLabel
    exact_mod_cast gap
  simp only [winnerDrop, if_neg (not_lt.mpr nonneg)]
  omega

theorem unsafe_of_edge (rank : ℕ → ℕ) (parents : ℕ → ℤ) (first finish base : ℕ)
    (tree : Sparse) (parentRank : ℤ) (consistent : Parents rank parents parentRank tree)
    (edge : ℕ × ℕ) (member : edge ∈ tree.edges) (incoming : Incoming first finish edge)
    (exceptional : parents edge.1 < (base : ℤ)) :
    edge ∈ unsafeEdges rank first finish base parentRank tree := by
  induction tree generalizing parentRank with
  | empty => simp [Sparse.edges] at member
  | node root left right il ir =>
      simp only [Sparse.edges, Finset.mem_union] at member
      rcases member with ((hl | hr) | hl) | hr
      · have child := il (rank root) consistent.2.1 hl
        simp only [unsafeEdges, Finset.mem_union]
        tauto
      · have child := ir (rank root) consistent.2.2 hr
        simp only [unsafeEdges, Finset.mem_union]
        tauto
      · have eq := (edgeTo_members hl).1
        have condition : parentRank < (base : ℤ) ∧ ¬ Inside first finish root ∧ Inside first finish edge.2 := by
          rw [eq, consistent.1] at exceptional
          exact ⟨exceptional, eq ▸ incoming.1, incoming.2⟩
        have head : edge ∈ unsafeTo first finish base root parentRank left := by
          cases left with
          | empty => simp [Sparse.edgeTo] at hl
          | node child l r =>
              have pairEq : edge = (root, child) := by simpa [Sparse.edgeTo] using hl
              subst edge
              simp [unsafeTo, condition]
        simp only [unsafeEdges, Finset.mem_union]
        tauto
      · have eq := (edgeTo_members hr).1
        have condition : parentRank < (base : ℤ) ∧ ¬ Inside first finish root ∧ Inside first finish edge.2 := by
          rw [eq, consistent.1] at exceptional
          exact ⟨exceptional, eq ▸ incoming.1, incoming.2⟩
        have head : edge ∈ unsafeTo first finish base root parentRank right := by
          cases right with
          | empty => simp [Sparse.edgeTo] at hr
          | node child l r =>
              have pairEq : edge = (root, child) := by simpa [Sparse.edgeTo] using hr
              subst edge
              simp [unsafeTo, condition]
        simp only [unsafeEdges, Finset.mem_union]
        tauto

theorem active_excess_bound (rank : ℕ → ℕ) (labels parents : ℕ → ℤ)
    (first finish base : ℕ) (K : ℤ) (tree : Sparse) (parentRank : ℤ)
    (ordered : tree.Ordered) (heap : tree.Heap rank)
    (consistent : Parents rank parents parentRank tree)
    (range : 1 ≤ K)
    (bounds : ∀ key ∈ tree.keys, 1 ≤ labels key ∧ labels key ≤ K)
    (floor : ∀ key ∈ tree.keys, Inside first finish key → base ≤ rank key)
    (source : ∀ key ∈ tree.keys, Inside first finish key → labels key = baseLabel rank base key) :
    (∑ edge ∈ tree.edges, excess rank labels parents first finish edge) ≤ K - 1 := by
  classical
  let exceptional := unsafeEdges rank first finish base parentRank tree
  have capacity : exceptional.card ≤ 1 := unsafe_card_le_one rank first finish base tree ordered heap floor parentRank
  have each : ∀ edge ∈ tree.edges, excess rank labels parents first finish edge ≤
      if edge ∈ exceptional then K - 1 else 0 := by
    intro edge member
    obtain ⟨parentMem, childMem⟩ := edge_members tree edge member
    have parentBounds := bounds edge.1 parentMem
    have childBounds := bounds edge.2 childMem
    have dropNonneg := winnerDrop_nonneg rank labels parents edge.1
    by_cases incoming : Incoming first finish edge
    · simp only [excess, if_pos incoming]
      by_cases safe : (base : ℤ) ≤ parents edge.1
      · have dropBound := safe_drop rank labels parents base edge safe
          (edge_rank_le rank tree heap edge member) (source edge.2 childMem incoming.2)
        split_ifs <;> omega
      · have unsafeMem : edge ∈ exceptional := unsafe_of_edge rank parents first finish base tree parentRank
          consistent edge member incoming (by omega)
        rw [if_pos unsafeMem]
        omega
    · simp only [excess, if_neg incoming]
      split_ifs <;> omega
  have total := Finset.sum_le_sum each
  have filterCapacity : (tree.edges.filter (fun edge => edge ∈ exceptional)).card ≤ 1 := by
    apply (Finset.card_le_card ?_).trans capacity
    intro edge member
    exact (Finset.mem_filter.mp member).2
  rw [← Finset.sum_filter] at total
  simp only [Finset.sum_const, nsmul_eq_mul] at total
  have castCapacity : ((tree.edges.filter (fun edge => edge ∈ exceptional)).card : ℤ) ≤ 1 := by
    exact_mod_cast filterCapacity
  have final := mul_le_mul_of_nonneg_right castCapacity (show 0 ≤ K - 1 by omega)
  omega

/-- The parent-rank map is computed from the actual sparse tree. -/
theorem actual_active_excess_bound (rank : ℕ → ℕ) (labels : ℕ → ℤ)
    (first finish base : ℕ) (K : ℤ) (tree : Sparse)
    (ordered : tree.Ordered) (heap : tree.Heap rank)
    (range : 1 ≤ K)
    (bounds : ∀ key ∈ tree.keys, 1 ≤ labels key ∧ labels key ≤ K)
    (floor : ∀ key ∈ tree.keys, Inside first finish key → base ≤ rank key)
    (source : ∀ key ∈ tree.keys, Inside first finish key → labels key = baseLabel rank base key) :
    (∑ edge ∈ tree.edges, excess rank labels (parentRanks rank (-1) tree) first finish edge) ≤ K - 1 :=
  active_excess_bound rank labels _ first finish base K tree (-1) ordered heap
    (parentRanks_correct rank tree ordered (-1)) range bounds floor source

/-- The two possible inactive entering edges add two label ranges.
The active estimate above only needs one range, so the full fringe
satisfies a slightly stronger bound than the manuscript's four. -/
theorem fringe_excess_bound {lo hi : ℕ} (rank owner : ℕ → ℕ) (labels : ℕ → ℤ)
    (tree : Splay.Tree.BST lo hi) (first finish base : ℕ) (K : ℤ)
    (projection : GreedyMerge.Fringe.Projection rank owner tree)
    (localOwners : GreedyMerge.Fringe.LocalOwners rank owner lo hi)
    (range : 1 ≤ K)
    (bounds : ∀ key, 2*lo ≤ key → key ≤ 2*hi → 1 ≤ labels key ∧ labels key ≤ K)
    (floor : ∀ key, 2*lo ≤ key → key ≤ 2*hi → Inside first finish key → base ≤ rank key)
    (source : ∀ key, 2*lo ≤ key → key ≤ 2*hi → Inside first finish key →
      labels key = baseLabel rank base key) :
    (∑ edge ∈ (GreedyMerge.Fringe.edges owner tree).toFinset,
      excess rank labels (parentRanks rank (-1) (active owner tree).tree) first finish edge) ≤
      3 * (K - 1) := by
  classical
  let parents := parentRanks rank (-1) (active owner tree).tree
  let edges := (GreedyMerge.Fringe.edges owner tree).toFinset
  let retained := edges.filter (fun edge => GreedyMerge.Fringe.Retained owner edge.2)
  let inactive := edges.filter (fun edge => ¬ GreedyMerge.Fringe.Retained owner edge.2)
  let f := excess rank labels parents first finish
  have activeEq : retained = (active owner tree).tree.edges :=
    (active_edges rank owner tree projection localOwners).symm
  have activeBound := actual_active_excess_bound rank labels first finish base K (active owner tree).tree
    (active_ordered rank owner tree projection localOwners)
    (active_heap rank owner tree projection localOwners) range
    (fun key member => let b := active_bounds owner tree key member; bounds key b.1 b.2)
    (fun key member => let b := active_bounds owner tree key member; floor key b.1 b.2)
    (fun key member => let b := active_bounds owner tree key member; source key b.1 b.2)
  change (∑ edge ∈ (active owner tree).tree.edges, f edge) ≤ K - 1 at activeBound
  rw [← activeEq] at activeBound
  let entering := inactive.filter (Incoming first finish)
  have support : entering ⊆ {(first-1,first), (finish,finish-1)} := by
    intro edge member
    obtain ⟨inactiveMem, condition⟩ := Finset.mem_filter.mp member
    obtain ⟨edgeMem, notRetained⟩ := Finset.mem_filter.mp inactiveMem
    have adjacent := inactive_edge_adjacent rank owner tree localOwners edge.1 edge.2
      (List.mem_toFinset.mp edgeMem) notRetained
    have cases : edge = (first-1,first) ∨ edge = (finish,finish-1) := by
      unfold Incoming Inside at condition
      rcases adjacent with left | right
      · left; apply Prod.ext <;> simp only <;> omega
      · right; apply Prod.ext <;> simp only <;> omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using cases
  have capacity : entering.card ≤ 2 := by
    have one := Finset.card_le_card support
    have two := Finset.card_insert_le (first-1,first) ({(finish,finish-1)} : Finset (ℕ × ℕ))
    simp only [Finset.card_singleton] at two
    omega
  have inactiveEq : (∑ edge ∈ inactive, f edge) = ∑ edge ∈ entering, f edge := by
    change (∑ edge ∈ inactive, f edge) = ∑ edge ∈ inactive.filter (Incoming first finish), f edge
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro edge member
    by_cases incoming : Incoming first finish edge
    · simp [incoming]
    · simp [f, excess, incoming]
  have each : ∀ edge ∈ entering, f edge ≤ K - 1 := by
    intro edge member
    have edgeMem := (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).1
    have b := GreedyMerge.Fringe.edge_strict_rank_and_bounds rank owner tree edge.1 edge.2
      projection (List.mem_toFinset.mp edgeMem)
    have winner := bounds edge.1 b.1 b.2.1
    have loser := bounds edge.2 b.2.2.1 b.2.2.2.1
    have nonneg := winnerDrop_nonneg rank labels parents edge.1
    dsimp only [f]
    unfold excess
    split_ifs <;> omega
  have inactiveBound : (∑ edge ∈ inactive, f edge) ≤ 2 * (K - 1) := by
    rw [inactiveEq]
    calc
      _ ≤ ∑ _edge ∈ entering, (K - 1) := Finset.sum_le_sum each
      _ = (entering.card : ℤ) * (K - 1) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (K - 1) := mul_le_mul_of_nonneg_right (by exact_mod_cast capacity) (by omega)
  have partition := Finset.sum_filter_add_sum_filter_not edges
    (fun edge => GreedyMerge.Fringe.Retained owner edge.2) f
  change (∑ edge ∈ retained, f edge) + (∑ edge ∈ inactive, f edge) = _ at partition
  change (∑ edge ∈ edges, f edge) ≤ _
  omega

end Greedy.NegativeBoundary
