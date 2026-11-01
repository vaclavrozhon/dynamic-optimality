import SparseActiveTree
import HistoricalKeyCuts
import PhaseBuckets

namespace GreedyForest.ActiveTree

open HistoricalCuts

def cutView (label : ℕ → ℤ) (cut : ℕ) : Sparse → CutTree
  | .empty => .empty
  | .node key left right =>
      .node (decide (cut ≤ key)) (label key) (cutView label cut left) (cutView label cut right)

theorem allSide_cutView (label : ℕ → ℤ) (cut : ℕ) (side : Bool) (tree : Sparse)
    (hside : ∀ v ∈ tree.keys, decide (cut ≤ v) = side) :
    AllSide side (cutView label cut tree) := by
  induction tree with
  | empty => trivial
  | node key left right ihLeft ihRight =>
      refine ⟨hside key (Sparse.root_mem _ _ _), ?_, ?_⟩
      · apply ihLeft
        intro v hv
        exact hside v (by simp [Sparse.keys,hv])
      · apply ihRight
        intro v hv
        exact hside v (by simp [Sparse.keys,hv])

theorem ordered_cutView (label : ℕ → ℤ) (cut : ℕ) (tree : Sparse)
    (ho : Sparse.Ordered tree) : CutOrdered (cutView label cut tree) := by
  induction tree with
  | empty => trivial
  | node key left right ihLeft ihRight =>
      refine ⟨ihLeft ho.1,ihRight ho.2.1,?_⟩
      by_cases hc : cut ≤ key
      · have hs : AllSide true (cutView label cut right) := by
          apply allSide_cutView
          intro v hv
          have h := ho.2.2.2 v hv
          simp only [decide_eq_true_eq]
          omega
        simpa [hc] using hs
      · have hs : AllSide false (cutView label cut left) := by
          apply allSide_cutView
          intro v hv
          have h := ho.2.2.1 v hv
          simp only [decide_eq_false_iff_not]
          omega
        simpa [hc] using hs

theorem bounded_cutView (rank : ℕ → ℕ) (label : ℕ → ℤ) (cut : ℕ)
    (tree : Sparse) (K lower : ℤ) (hh : Sparse.Heap rank tree)
    (hm : ∀ a b, rank a ≤ rank b → label a ≤ label b)
    (hb : ∀ v ∈ tree.keys, lower ≤ label v ∧ label v ≤ K) :
    LabelBounded K lower (cutView label cut tree) := by
  induction tree generalizing lower with
  | empty => trivial
  | node key left right ihLeft ihRight =>
      have hk := hb key (Sparse.root_mem _ _ _)
      refine ⟨hk.1,hk.2,?_,?_⟩
      · apply ihLeft (label key) hh.1
        intro v hv
        have hmax := (hb v (by simp [Sparse.keys,hv])).2
        exact ⟨hm key v (hh.2.2.1 v hv), hmax⟩
      · apply ihRight (label key) hh.2.1
        intro v hv
        have hmax := (hb v (by simp [Sparse.keys,hv])).2
        exact ⟨hm key v (hh.2.2.2 v hv), hmax⟩

theorem opposite_sides_iff (cut a b : ℕ) :
    decide (cut ≤ b) ≠ decide (cut ≤ a) ↔ KeyCrosses cut a b := by
  unfold KeyCrosses
  by_cases ha : cut ≤ a <;> by_cases hb : cut ≤ b <;> simp [ha,hb] <;> omega

def StrictCrosses (label : ℕ → ℤ) (cut : ℕ) (edge : ℕ × ℕ) : Prop :=
  KeyCrosses cut edge.1 edge.2 ∧ label edge.1 < label edge.2

instance (label : ℕ → ℤ) (cut : ℕ) (edge : ℕ × ℕ) :
    Decidable (StrictCrosses label cut edge) := inferInstanceAs (Decidable (_ ∧ _))

def strictCrossingEdges (label : ℕ → ℤ) (cut : ℕ) (tree : Sparse) : Finset (ℕ × ℕ) :=
  tree.edges.filter (StrictCrosses label cut)

theorem edgeTo_strict_card (label : ℕ → ℤ) (cut parent : ℕ) (tree : Sparse) :
    ((tree.edgeTo parent).filter (StrictCrosses label cut)).card =
      (edgeBad (decide (cut ≤ parent)) (label parent) (cutView label cut tree)).toNat := by
  cases tree with
  | empty => simp [Sparse.edgeTo,cutView,edgeBad]
  | node key left right =>
      simp only [Sparse.edgeTo,cutView,edgeBad,opposite_sides_iff]
      simp only [Finset.filter_singleton,StrictCrosses]
      split_ifs <;> simp

theorem edgeBad_nonnegative (side : Bool) (label : ℤ) (tree : CutTree) :
    0 ≤ edgeBad side label tree := by
  cases tree with
  | empty => simp [edgeBad]
  | node side' label' left right =>
      simp only [edgeBad]
      split_ifs <;> omega

/-- Actual distinct crossing edges are bounded by the cut-view tree
count. Using an inequality avoids needing a separate edge-list nodup
claim for this structural step. -/
theorem strictCrossingEdges_card_le_count (label : ℕ → ℤ) (cut : ℕ) (tree : Sparse) :
    ((strictCrossingEdges label cut tree).card : ℤ) ≤ badCutCount (cutView label cut tree) := by
  induction tree with
  | empty => simp [strictCrossingEdges,Sparse.edges,cutView,badCutCount]
  | node key left right ihLeft ihRight =>
      let a := strictCrossingEdges label cut left
      let b := strictCrossingEdges label cut right
      let c := (left.edgeTo key).filter (StrictCrosses label cut)
      let d := (right.edgeTo key).filter (StrictCrosses label cut)
      have heq : strictCrossingEdges label cut (.node key left right) = a ∪ b ∪ c ∪ d := by
        simp [strictCrossingEdges,Sparse.edges,Finset.filter_union,a,b,c,d]
      have h1 := Finset.card_union_le a b
      have h2 := Finset.card_union_le (a ∪ b) c
      have h3 := Finset.card_union_le (a ∪ b ∪ c) d
      have hcard : ((a ∪ b ∪ c ∪ d).card : ℤ) ≤
          (a.card:ℤ) + (b.card:ℤ) + (c.card:ℤ) + (d.card:ℤ) := by
        exact_mod_cast (show (a ∪ b ∪ c ∪ d).card ≤ a.card+b.card+c.card+d.card by omega)
      have hc := edgeTo_strict_card label cut key left
      have hd := edgeTo_strict_card label cut key right
      have hc0 := edgeBad_nonnegative (decide (cut ≤ key)) (label key) (cutView label cut left)
      have hd0 := edgeBad_nonnegative (decide (cut ≤ key)) (label key) (cutView label cut right)
      have hci : (c.card:ℤ) = edgeBad (decide (cut ≤ key)) (label key) (cutView label cut left) := by
        dsimp [c]
        rw [hc,Int.toNat_of_nonneg hc0]
      have hdi : (d.card:ℤ) = edgeBad (decide (cut ≤ key)) (label key) (cutView label cut right) := by
        dsimp [d]
        rw [hd,Int.toNat_of_nonneg hd0]
      rw [heq]
      change (↑(a ∪ b ∪ c ∪ d).card : ℤ) ≤
        badCutCount (cutView label cut left) + badCutCount (cutView label cut right) +
          edgeBad (decide (cut ≤ key)) (label key) (cutView label cut left) +
          edgeBad (decide (cut ≤ key)) (label key) (cutView label cut right)
      dsimp only [a,b] at hcard
      linarith

end GreedyForest.ActiveTree
