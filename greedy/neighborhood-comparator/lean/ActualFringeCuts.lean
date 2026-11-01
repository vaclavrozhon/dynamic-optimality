import SparseCutGeometry
import FringeSchedule

/-!
Strict-rise cut counts for the literal edge set of a canonical fringe.
The active sparse BST is constructed, and the inactive exceptions are
derived from the adjacent-gap parent theorem. No event-to-cut projection
or phase capacity is assumed in the resulting theorem.
-/
namespace GreedyForest.ActiveTree

open Splay.Tree Splay.Tree.BST
open GreedyMerge.Fringe
open GreedyMerge.Fringe.Schedule
open HistoricalCuts

theorem inactive_edge_adjacent {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hloc : LocalOwners rank owner lo hi) (parent child : ℕ)
    (he : (parent,child) ∈ GreedyMerge.Fringe.edges owner tree)
    (hn : ¬Retained owner child) : parent+1=child ∨ child+1=parent := by
  have hm : child % 2 ≠ 0 := fun h => hn (Or.inl h)
  have hmod : child % 2 = 1 := by omega
  have hdiv := Nat.mod_add_div child 2
  have heq : child = 2*(child/2)+1 := by omega
  have ho := (mem_edges_iff_outgoing owner tree parent child).mp he
  rw [heq] at ho hn
  have hex := (inactive_parent_exact rank owner tree parent (child/2) hn hloc).mp ho
  have hgap := (inactive_parent_is_gap hloc hex.1 hex.2.1 hn).1
  rcases hgap with h | h <;> omega

theorem adjacent_crossing_cases {cut parent child : ℕ}
    (ha : parent+1=child ∨ child+1=parent) (hc : KeyCrosses cut parent child) :
    (parent,child) = (cut-1,cut) ∨ (parent,child) = (cut,cut-1) := by
  unfold KeyCrosses at hc
  rcases ha with ha | ha <;> rcases hc with hc | hc
  · left; congr <;> omega
  · omega
  · omega
  · right; congr <;> omega

def fringeStrictCuts (owner : ℕ → ℕ) (label : ℕ → ℤ) (cut : ℕ)
    {lo hi : ℕ} (tree : BST lo hi) : Finset (ℕ × ℕ) :=
  (GreedyMerge.Fringe.edges owner tree).toFinset.filter (StrictCrosses label cut)

theorem fringe_strict_cuts_subset {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (label : ℕ → ℤ) (cut : ℕ) :
    fringeStrictCuts owner label cut tree ⊆
      strictCrossingEdges label cut (active owner tree).tree ∪ {(cut-1,cut),(cut,cut-1)} := by
  intro edge he
  obtain ⟨parent,child⟩ := edge
  obtain ⟨hedge,hstrict⟩ := Finset.mem_filter.mp he
  have hedge' := List.mem_toFinset.mp hedge
  by_cases hr : Retained owner child
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨?_,hstrict⟩
    rw [active_edges rank owner tree hp hloc]
    exact Finset.mem_filter.mpr ⟨hedge,hr⟩
  · apply Finset.mem_union_right
    have hadj := inactive_edge_adjacent rank owner tree hloc parent child hedge' hr
    rcases adjacent_crossing_cases hadj hstrict.1 with h | h <;> simp [h]

/-- The actual fringe edges admit the literal active-cut-tree capacity
plus two adjacent inactive slots, before using any bound on label levels. -/
theorem fringe_strict_cut_path_bound {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (hp : Projection rank owner tree)
    (hloc : LocalOwners rank owner lo hi) (label : ℕ → ℤ) (cut : ℕ) :
    (fringeStrictCuts owner label cut tree).card ≤
      (badCutCount (cutView label cut (active owner tree).tree)).toNat + 2 := by
  have hs := fringe_strict_cuts_subset rank owner tree hp hloc label cut
  have hc1 := Finset.card_le_card hs
  have hc2 := Finset.card_union_le
    (strictCrossingEdges label cut (active owner tree).tree)
    ({(cut-1,cut),(cut,cut-1)} : Finset (ℕ × ℕ))
  have hc3 : ({(cut-1,cut),(cut,cut-1)} : Finset (ℕ × ℕ)).card ≤ 2 := by
    have h := Finset.card_insert_le (cut-1,cut) ({(cut,cut-1)} : Finset (ℕ × ℕ))
    simpa using h
  have he := strictCrossingEdges_card_le_count label cut (active owner tree).tree
  have hn : (strictCrossingEdges label cut (active owner tree).tree).card ≤
      (badCutCount (cutView label cut (active owner tree).tree)).toNat := by omega
  omega

/-- Every strict-rise edge crossing one spatial cut in the actual
canonical fringe is paid by one of at most K−1 active path rises or at
most two adjacent inactive edges. -/
theorem fringe_strict_cut_bound {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (label : ℕ → ℤ) (cut : ℕ) (K : ℤ) (hK : 1 ≤ K)
    (hm : ∀ a b, rank a ≤ rank b → label a ≤ label b)
    (hb : ∀ v, 2*lo ≤ v → v ≤ 2*hi → 1 ≤ label v ∧ label v ≤ K) :
    ((fringeStrictCuts owner label cut tree).card : ℤ) ≤ K+1 := by
  let a := (active owner tree).tree
  have ho := active_ordered rank owner tree hp hloc
  have hh := active_heap rank owner tree hp hloc
  have hb' : ∀ v ∈ a.keys, 1 ≤ label v ∧ label v ≤ K := by
    intro v hv
    have hbounds := active_bounds owner tree v hv
    exact hb v hbounds.1 hbounds.2
  have ht := badCutCount_le_levels K 1 (cutView label cut a) hK
    (ordered_cutView label cut a ho) (bounded_cutView rank label cut a K 1 hh hm hb')
  have he := strictCrossingEdges_card_le_count label cut a
  have hs := fringe_strict_cuts_subset rank owner tree hp hloc label cut
  change fringeStrictCuts owner label cut tree ⊆
    strictCrossingEdges label cut a ∪ {(cut-1,cut),(cut,cut-1)} at hs
  have hc1 := Finset.card_le_card hs
  have hc2 := Finset.card_union_le (strictCrossingEdges label cut a)
    ({(cut-1,cut),(cut,cut-1)} : Finset (ℕ × ℕ))
  have hc3 : ({(cut-1,cut),(cut,cut-1)} : Finset (ℕ × ℕ)).card ≤ 2 := by
    have h := Finset.card_insert_le (cut-1,cut) ({(cut,cut-1)} : Finset (ℕ × ℕ))
    simpa using h
  have hc : (fringeStrictCuts owner label cut tree).card ≤
      (strictCrossingEdges label cut a).card + 2 := by omega
  have hci : ((fringeStrictCuts owner label cut tree).card : ℤ) ≤
      ((strictCrossingEdges label cut a).card : ℤ) + 2 := by exact_mod_cast hc
  linarith

end GreedyForest.ActiveTree

#print axioms GreedyForest.ActiveTree.fringe_strict_cut_bound
