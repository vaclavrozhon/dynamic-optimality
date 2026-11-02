import DynamicOptimality.Funnel.WarmCartesian
import ChaCha.ConvexSearchQuotient

/-! # The template is the actual convex quotient of the warm tree

This bridge reuses the existing integer-cell quotient. It identifies its tree
exactly with the Cartesian tree of the interval-visit word, including repeated
labels, unused cells, and clipping to a proper interval of cell labels.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree ChaCha.ConvexSearchQuotient

def clipped (label : Int → Int) (lo hi : Int) (history : List Int) : List Int :=
  (history.filter (fun y => decide (lo ≤ label y ∧ label y ≤ hi))).map label

private theorem key_lt_of_label_lt {label : Int → Int} (mono : Monotone label)
    {a b : Int} (strict : label a < label b) : a < b := by
  by_contra failed
  have := mono (show b ≤ a by omega)
  omega

private theorem clipped_right (label : Int → Int) (mono : Monotone label)
    (rest : List Int) (a lo hi : Int) (below : label a < lo) :
    clipped label lo hi (rest.filter (fun y => decide (a < y))) = clipped label lo hi rest := by
  unfold clipped
  rw [List.filter_filter]
  apply congrArg (List.map label)
  apply List.filter_congr
  intro y _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨And.left,fun range => ⟨range,key_lt_of_label_lt mono (by omega)⟩⟩

private theorem clipped_left (label : Int → Int) (mono : Monotone label)
    (rest : List Int) (a lo hi : Int) (above : hi < label a) :
    clipped label lo hi (rest.filter (fun y => decide (y < a))) = clipped label lo hi rest := by
  unfold clipped
  rw [List.filter_filter]
  apply congrArg (List.map label)
  apply List.filter_congr
  intro y _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨And.left,fun range => ⟨range,key_lt_of_label_lt mono (by omega)⟩⟩

private theorem clipped_left_child (label : Int → Int) (mono : Monotone label)
    (rest : List Int) (a lo hi : Int) (upper : label a ≤ hi) :
    clipped label lo (label a - 1) (rest.filter (fun y => decide (y < a))) =
      (clipped label lo hi rest).filter (fun z => decide (z < label a)) := by
  unfold clipped
  rw [List.filter_map]
  simp only [List.filter_filter,Function.comp_apply]
  apply congrArg (List.map label)
  apply List.filter_congr
  intro y _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨by omega,by omega,by omega⟩
  · intro h
    exact ⟨⟨by omega,by omega⟩,key_lt_of_label_lt mono h.1⟩

private theorem clipped_right_child (label : Int → Int) (mono : Monotone label)
    (rest : List Int) (a lo hi : Int) (lower : lo ≤ label a) :
    clipped label (label a + 1) hi (rest.filter (fun y => decide (a < y))) =
      (clipped label lo hi rest).filter (fun z => decide (label a < z)) := by
  unfold clipped
  rw [List.filter_map]
  simp only [List.filter_filter,Function.comp_apply]
  apply congrArg (List.map label)
  apply List.filter_congr
  intro y _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨by omega,by omega,by omega⟩
  · intro h
    exact ⟨⟨by omega,by omega⟩,key_lt_of_label_lt mono h.1⟩

theorem project_cartesian (label : Int → Int) (mono : Monotone label)
    (history : List Int) (lo hi : Int) :
    project label lo hi (cartesian history) = cartesian (clipped label lo hi history) := by
  induction history using length_induction generalizing lo hi with
  | step history ih =>
    cases history with
    | nil => simp [clipped,project]
    | cons a rest =>
      have leftLength : (rest.filter (fun y => decide (y < a))).length < (a::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (a < y))).length < (a::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      rw [cartesian_cons]
      by_cases below : label a < lo
      · have outside : ¬ (lo ≤ label a ∧ label a ≤ hi) := by omega
        simp only [project,below,↓reduceIte,ih _ rightLength,clipped_right label mono rest a lo hi below]
        simp [clipped,outside]
      · by_cases above : hi < label a
        · have outside : ¬ (lo ≤ label a ∧ label a ≤ hi) := by omega
          simp only [project,below,above,↓reduceIte,ih _ leftLength,clipped_left label mono rest a lo hi above]
          simp [clipped,outside]
        · have lower : lo ≤ label a := by omega
          have upper : label a ≤ hi := by omega
          have split : clipped label lo hi (a :: rest) = label a :: clipped label lo hi rest := by
            simp [clipped,lower,upper]
          simp only [project,below,above,↓reduceIte,split,cartesian_cons,
            ih _ leftLength,ih _ rightLength]
          rw [clipped_left_child label mono rest a lo hi upper,
            clipped_right_child label mono rest a lo hi lower]

end DynamicOptimality.Funnel.Warm
