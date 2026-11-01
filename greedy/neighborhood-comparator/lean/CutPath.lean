import Mathlib

/-!
A binary search tree viewed relative to one spatial cut. `false` means
left of the cut and `true` means right of it. No geometric representation
is assumed here: `CutOrdered` states precisely the required inorder fact.
-/
namespace GreedyForest

inductive CutTree where
  | empty : CutTree
  | node (side : Bool) (label : ℤ) (left right : CutTree) : CutTree
  deriving DecidableEq

open CutTree

def AllSide (side : Bool) : CutTree → Prop
  | empty => True
  | node s _ l r => s = side ∧ AllSide side l ∧ AllSide side r

def CutOrdered : CutTree → Prop
  | empty => True
  | node side _ l r => CutOrdered l ∧ CutOrdered r ∧
      (if side then AllSide true r else AllSide false l)

def LabelBounded (K lower : ℤ) : CutTree → Prop
  | empty => True
  | node _ q l r => lower ≤ q ∧ q ≤ K ∧
      LabelBounded K q l ∧ LabelBounded K q r

def edgeBad (parentSide : Bool) (parentLabel : ℤ) : CutTree → ℤ
  | empty => 0
  | node side label _ _ => if side ≠ parentSide ∧ parentLabel < label then 1 else 0

def badCutCount : CutTree → ℤ
  | empty => 0
  | node side label l r =>
      badCutCount l + badCutCount r + edgeBad side label l + edgeBad side label r

theorem edgeBad_eq_zero_same_side (s : Bool) (q : ℤ) (t : CutTree)
    (h : AllSide s t) : edgeBad s q t = 0 := by
  cases t with
  | empty => rfl
  | node side label l r =>
      simp only [AllSide] at h
      simp [edgeBad, h.1]

theorem badCutCount_eq_zero_same_side (s : Bool) (t : CutTree)
    (h : AllSide s t) : badCutCount t = 0 := by
  induction t with
  | empty => rfl
  | node side label l r il ir =>
      simp only [AllSide] at h
      rcases h with ⟨hs, hl, hr⟩
      subst side
      have hzl := il hl
      have hzr := ir hr
      have hel := edgeBad_eq_zero_same_side s label l hl
      have her := edgeBad_eq_zero_same_side s label r hr
      simp [badCutCount, hzl, hzr, hel, her]

theorem edgeBad_le_label_jump (s t : Bool) (q z : ℤ) (l r : CutTree)
    (h : q ≤ z) : edgeBad s q (node t z l r) ≤ z - q := by
  dsimp only [edgeBad]
  split_ifs with he
  · omega
  · omega

/-- On a cut-ordered tree, every strictly rising edge crossing the cut
consumes one label level on its single search path. Edges may be omitted
from this count; no alternation or cancellation of their directions is
assumed. -/
theorem badCutCount_le_levels (K lower : ℤ) (t : CutTree)
    (hlo : lower ≤ K) (hordered : CutOrdered t)
    (hlabels : LabelBounded K lower t) :
    badCutCount t ≤ K - lower := by
  induction t generalizing lower with
  | empty => simp [badCutCount]; omega
  | node side q l r il ir =>
      rcases hlabels with ⟨hlq, hqK, hll, hlr⟩
      rcases hordered with ⟨hol, hor, hside⟩
      cases side
      · simp only [Bool.false_eq_true, ↓reduceIte] at hside
        have hzero := badCutCount_eq_zero_same_side false l hside
        have hezero := edgeBad_eq_zero_same_side false q l hside
        cases r with
        | empty =>
            change badCutCount l + 0 + edgeBad false q l + 0 ≤ K - lower
            rw [hzero, hezero]
            omega
        | node sr qr lr rr =>
            rcases hlr with ⟨hqqr, hqrK, hlrl, hlrr⟩
            have hir := ir qr hqrK hor ⟨le_refl qr, hqrK, hlrl, hlrr⟩
            have he := edgeBad_le_label_jump false sr q qr lr rr hqqr
            simp only [badCutCount, hzero, hezero, zero_add, add_zero]
            change badCutCount (node sr qr lr rr) + edgeBad false q (node sr qr lr rr) ≤ K - lower
            omega
      · simp only [↓reduceIte] at hside
        have hzero := badCutCount_eq_zero_same_side true r hside
        have hezero := edgeBad_eq_zero_same_side true q r hside
        cases l with
        | empty =>
            change 0 + badCutCount r + 0 + edgeBad true q r ≤ K - lower
            rw [hzero, hezero]
            omega
        | node sl ql ll rl =>
            rcases hll with ⟨hqql, hqlK, hlll, hllr⟩
            have hil := il ql hqlK hol ⟨le_refl ql, hqlK, hlll, hllr⟩
            have he := edgeBad_le_label_jump true sl q ql ll rl hqql
            simp only [badCutCount, hzero, hezero, add_zero]
            change badCutCount (node sl ql ll rl) + edgeBad true q (node sl ql ll rl) ≤ K - lower
            omega

end GreedyForest
