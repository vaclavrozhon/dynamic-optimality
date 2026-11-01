import CutPath

/-!
# Weighted edges across an inorder cut

`CutTree` records which side of a fixed key cut each node occupies.
`CutOrdered` says the subtree away from the cut stays on that side.
`LabelBounded K lower` says labels increase down edges and stay between
`lower` and `K`. The sum of label increases across the cut is bounded by
the whole label range, even when there are many crossings.
-/

namespace Greedy.WeightedCut

open GreedyForest GreedyForest.CutTree

def edgeWeight (parentSide : Bool) (parentLabel : ℤ) : CutTree → ℤ
  | .empty => 0
  | .node side label _ _ => if side ≠ parentSide then label - parentLabel else 0

def weight : CutTree → ℤ
  | .empty => 0
  | .node side label left right =>
      weight left + weight right + edgeWeight side label left + edgeWeight side label right

theorem edgeWeight_same (side : Bool) (label : ℤ) (tree : CutTree)
    (same : AllSide side tree) : edgeWeight side label tree = 0 := by
  cases tree with
  | empty => rfl
  | node s q left right => simp [edgeWeight, same.1]

theorem weight_same (side : Bool) (tree : CutTree) (same : AllSide side tree) :
    weight tree = 0 := by
  induction tree with
  | empty => rfl
  | node s q left right il ir =>
      obtain ⟨hs, hl, hr⟩ := same
      subst s
      simp [weight, il hl, ir hr, edgeWeight_same side q left hl,
        edgeWeight_same side q right hr]

theorem edgeWeight_le (s t : Bool) (q r : ℤ) (left right : CutTree) (mono : q ≤ r) :
    edgeWeight s q (.node t r left right) ≤ r - q := by
  dsimp only [edgeWeight]
  split_ifs <;> omega

theorem weight_le_range (K lower : ℤ) (tree : CutTree) (range : lower ≤ K)
    (ordered : CutOrdered tree) (labels : LabelBounded K lower tree) :
    weight tree ≤ K - lower := by
  induction tree generalizing lower with
  | empty => simp [weight]; omega
  | node side q left right il ir =>
      obtain ⟨hlq, hqK, hleft, hright⟩ := labels
      obtain ⟨ol, or, same⟩ := ordered
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte] at same
        have wz := weight_same false left same
        have ez := edgeWeight_same false q left same
        cases right with
        | empty =>
            change weight left + 0 + edgeWeight false q left + 0 ≤ _
            rw [wz, ez]
            omega
        | node s r l rr =>
            obtain ⟨hqr, hrK, hrl, hrr⟩ := hright
            have bound := ir r hrK or ⟨le_rfl, hrK, hrl, hrr⟩
            have edgeBound := edgeWeight_le false s q r l rr hqr
            change weight left + weight (.node s r l rr) +
              edgeWeight false q left + edgeWeight false q (.node s r l rr) ≤ _
            rw [wz, ez]
            omega
      · simp only [↓reduceIte] at same
        have wz := weight_same true right same
        have ez := edgeWeight_same true q right same
        cases left with
        | empty =>
            change 0 + weight right + 0 + edgeWeight true q right ≤ _
            rw [wz, ez]
            omega
        | node s r ll rr =>
            obtain ⟨hqr, hrK, hrl, hrr⟩ := hleft
            have bound := il r hrK ol ⟨le_rfl, hrK, hrl, hrr⟩
            have edgeBound := edgeWeight_le true s q r ll rr hqr
            change weight (.node s r ll rr) + weight right +
              edgeWeight true q (.node s r ll rr) + edgeWeight true q right ≤ _
            rw [wz, ez]
            omega

end Greedy.WeightedCut
