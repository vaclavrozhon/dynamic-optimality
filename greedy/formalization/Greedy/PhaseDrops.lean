import Greedy.NegativeBoundary

/-!
# Paying repeated winner charges by actual losing updates

Each record wins at most four times in a consolidation. Its parent in
the active tree is its eventual winning parent, so the corresponding
label drop is an actual loser update. The surviving root has zero drop.
The finite double count below makes the multiplicity four explicit.
-/

namespace Greedy.PhaseDrops

open Splay.Tree GreedyMerge.Fringe GreedyMerge.Fringe.Schedule
open GreedyForest.ActiveTree GreedyForest.Phase Splay.Analysis
open Greedy.NegativeBoundary
open scoped BigOperators

theorem outgoing_charge_bound {Record : Type*} [DecidableEq Record]
    (edges : Finset (Record × Record)) (charge : Record → ℤ) (drop : Record × Record → ℤ)
    (capacity : ℕ) (nonneg : ∀ edge ∈ edges, 0 ≤ drop edge)
    (chargeNonneg : ∀ key ∈ edges.image Prod.fst, 0 ≤ charge key)
    (degree : ∀ key ∈ edges.image Prod.fst, (edges.filter (fun edge => edge.1 = key)).card ≤ capacity)
    (paid : ∀ key ∈ edges.image Prod.fst, charge key ≤
      ∑ edge ∈ edges.filter (fun edge => edge.2 = key), drop edge) :
    (∑ edge ∈ edges, charge edge.1) ≤ (capacity : ℤ) * ∑ edge ∈ edges, drop edge := by
  classical
  let vertices := edges.image Prod.fst
  have partition := Finset.sum_fiberwise_of_maps_to' (s := edges) (t := vertices) (g := Prod.fst)
    (fun edge member => Finset.mem_image_of_mem Prod.fst member) charge
  change (∑ key ∈ vertices, ∑ _edge ∈ edges.filter (fun edge => edge.1 = key), charge key) = _ at partition
  rw [← partition]
  have localBound : ∀ key ∈ vertices,
      (∑ _edge ∈ edges.filter (fun edge => edge.1 = key), charge key) ≤
        (capacity : ℤ) * ∑ edge ∈ edges.filter (fun edge => edge.2 = key), drop edge := by
    intro key member
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (capacity : ℤ) * charge key := mul_le_mul_of_nonneg_right
        (by exact_mod_cast degree key member) (chargeNonneg key member)
      _ ≤ _ := mul_le_mul_of_nonneg_left (paid key member) (by positivity)
  calc
    _ ≤ ∑ key ∈ vertices, (capacity : ℤ) * ∑ edge ∈ edges.filter (fun edge => edge.2 = key), drop edge :=
      Finset.sum_le_sum localBound
    _ = (capacity : ℤ) * ∑ edge ∈ edges.filter (fun edge => edge.2 ∈ vertices), drop edge := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_eq_sum_filter]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun edge member _ => nonneg edge member))
      (by positivity)

def edgeDrop (rank : ℕ → ℕ) (initial : ℕ → ℤ) (edge : ℕ × ℕ) : ℤ :=
  max 0 (initial edge.2 - (contractedGap (rank edge.2 - rank edge.1) : ℤ))

theorem actual_drop {rank : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (run : Run rank events before after) (distinct : before.Nodup)
    (initial : ℕ → ℤ) (i : Fin events.length) :
    max 0 (labelsAt rank initial events i (events.get i).2 -
      labelsAt rank initial events (i.val+1) (events.get i).2) = edgeDrop rank initial (events.get i) := by
  rw [labelsAt_succ, (actual_event_source_labels run distinct initial i).2]
  simp only [linkLabels, Function.update_self, edgeDrop]

theorem parent_retained {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (localOwners : LocalOwners rank owner lo hi) (edge : ℕ × ℕ)
    (member : edge ∈ edges owner tree) : Retained owner edge.1 := by
  induction tree with
  | empty => simp [edges] at member
  | @node lo root hi left right il ir =>
      have lower := left.lower_le_upper
      have upper := right.lower_le_upper
      simp only [edges, List.mem_append, List.mem_map] at member
      rcases member with (hl | hr) | ⟨key, _, equal⟩
      · exact il (fun k kl ku => localOwners k kl (by omega)) hl
      · exact ir (fun k kl ku => localOwners k (by omega) ku) hr
      · have same : owner root = edge.1 := congrArg Prod.fst equal
        rw [← same]
        exact owner_retained localOwners lower (by omega)

theorem winner_drop_eq_edge {lo hi : ℕ} (rank owner : ℕ → ℕ) (initial : ℕ → ℤ)
    (tree : BST lo hi) (projection : Projection rank owner tree)
    (localOwners : LocalOwners rank owner lo hi) (edge : ℕ × ℕ)
    (member : edge ∈ edges owner tree) (retained : Retained owner edge.2) :
    winnerDrop rank initial (parentRanks rank (-1) (active owner tree).tree) edge.2 =
      edgeDrop rank initial edge := by
  have activeMem : edge ∈ (active owner tree).tree.edges := by
    rw [active_edges rank owner tree projection localOwners]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr member, retained⟩
  have parent := Parents.edge rank _ _ (-1)
    (parentRanks_correct rank _ (active_ordered rank owner tree projection localOwners) (-1)) edge activeMem
  simp only [winnerDrop, parent, Int.natCast_nonneg, not_lt.mpr, ↓reduceIte, Int.toNat_natCast, edgeDrop]

theorem winner_charges_le_four_drops {lo hi : ℕ} (rank owner : ℕ → ℕ) (initial : ℕ → ℤ)
    (tree : BST lo hi) (projection : Projection rank owner tree)
    (localOwners : LocalOwners rank owner lo hi) :
    (∑ edge ∈ (edges owner tree).toFinset,
      winnerDrop rank initial (parentRanks rank (-1) (active owner tree).tree) edge.1) ≤
      4 * ∑ edge ∈ (edges owner tree).toFinset, edgeDrop rank initial edge := by
  classical
  let parents := parentRanks rank (-1) (active owner tree).tree
  have nonneg : ∀ edge, 0 ≤ edgeDrop rank initial edge := fun _ => le_max_left _ _
  apply outgoing_charge_bound (edges owner tree).toFinset (winnerDrop rank initial parents)
    (edgeDrop rank initial) 4 (fun edge _ => nonneg edge)
    (fun key _ => winnerDrop_nonneg rank initial parents key)
  · intro key _
    calc
      _ = ((edges owner tree).filter (fun edge => edge.1 == key)).toFinset.card := by
        simp only [List.toFinset_filter, beq_iff_eq]
      _ ≤ ((edges owner tree).filter (fun edge => edge.1 == key)).length := List.toFinset_card_le _
      _ = (outgoing owner key tree).length := by
        rw [← List.countP_eq_length_filter, edges_winner_count]
      _ ≤ 4 := outgoing_degree_le_four rank owner tree key projection localOwners
  · intro key member
    obtain ⟨out, outMem, keyEq⟩ := Finset.mem_image.mp member
    have bounds := edge_strict_rank_and_bounds rank owner tree out.1 out.2 projection
      (List.mem_toFinset.mp outMem)
    have retained : Retained owner key := keyEq ▸ parent_retained rank owner tree localOwners out
      (List.mem_toFinset.mp outMem)
    by_cases root : key = treeOwner owner tree
    · have zero : winnerDrop rank initial parents key = 0 := by
        rw [root, ← active_root_eq rank owner tree projection localOwners]
        simp [parents, winnerDrop, parentRanks, Rooted.tree]
      rw [zero]
      exact Finset.sum_nonneg fun edge _ => nonneg edge
    · obtain ⟨parent, incoming⟩ := incoming_parent_exists rank owner tree key projection localOwners
        (by simpa only [keyEq] using bounds.1) (by simpa only [keyEq] using bounds.2.1) root
      have exactDrop := winner_drop_eq_edge rank owner initial tree projection localOwners
        (parent, key) incoming retained
      change winnerDrop rank initial parents key = _ at exactDrop
      rw [exactDrop]
      apply Finset.single_le_sum (fun edge _ => nonneg edge)
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr incoming, rfl⟩

end Greedy.PhaseDrops
