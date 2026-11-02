import DynamicOptimality.Funnel.WarmCartesian

/-! # Cartesian restriction to a key interval

Pruning the Cartesian tree below or above a cut produces exactly the
Cartesian tree of the retained occurrences, with no change of priorities.
The equalities include repeated keys and empty sides of the cut.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

def below (cut : α) : Tree α → Tree α
  | .empty => .empty
  | .node l x r => if x < cut then .node (below cut l) x (below cut r) else below cut l

def above (cut : α) : Tree α → Tree α
  | .empty => .empty
  | .node l x r => if cut < x then .node (above cut l) x (above cut r) else above cut r

private theorem filter_lt_lt (history : List α) (x cut : α) (h : ¬ x < cut) :
    (history.filter (fun y => decide (y < x))).filter (fun y => decide (y < cut)) =
      history.filter (fun y => decide (y < cut)) := by
  simp only [List.filter_filter, ← Bool.decide_and]
  apply List.filter_congr
  intro y _
  congr 1
  exact propext ⟨And.left, fun hy => ⟨hy, hy.trans_le (le_of_not_gt h)⟩⟩

private theorem filter_gt_gt (history : List α) (x cut : α) (h : ¬ cut < x) :
    (history.filter (fun y => decide (x < y))).filter (fun y => decide (cut < y)) =
      history.filter (fun y => decide (cut < y)) := by
  simp only [List.filter_filter, ← Bool.decide_and]
  apply List.filter_congr
  intro y _
  congr 1
  exact propext ⟨And.left, fun hy => ⟨hy, (le_of_not_gt h).trans_lt hy⟩⟩

theorem below_cartesian (history : List α) (cut : α) :
    below cut (cartesian history) =
      cartesian (history.filter (fun y => decide (y < cut))) := by
  induction history using length_induction with
  | step history ih =>
    cases history with
    | nil => simp [below]
    | cons x rest =>
      have leftLength : (rest.filter (fun y => decide (y < x))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (x < y))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      rw [cartesian_cons]
      by_cases h : x < cut
      · simp only [below, h, ↓reduceIte, List.filter_cons, decide_true,
          Bool.true_eq, ↓reduceIte, cartesian_cons]
        rw [ih _ leftLength, ih _ rightLength]
        congr 1 <;> congr 1 <;> exact List.filter_comm _ _ _
      · simp only [below, h, ↓reduceIte, List.filter_cons, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        rw [ih _ leftLength, filter_lt_lt rest x cut h]

theorem above_cartesian (history : List α) (cut : α) :
    above cut (cartesian history) =
      cartesian (history.filter (fun y => decide (cut < y))) := by
  induction history using length_induction with
  | step history ih =>
    cases history with
    | nil => simp [above]
    | cons x rest =>
      have leftLength : (rest.filter (fun y => decide (y < x))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      have rightLength : (rest.filter (fun y => decide (x < y))).length < (x::rest).length :=
        (List.length_filter_le _ _).trans_lt (by simp)
      rw [cartesian_cons]
      by_cases h : cut < x
      · simp only [above, h, ↓reduceIte, List.filter_cons, decide_true,
          Bool.true_eq, ↓reduceIte, cartesian_cons]
        rw [ih _ leftLength, ih _ rightLength]
        congr 1 <;> congr 1 <;> exact List.filter_comm _ _ _
      · simp only [above, h, ↓reduceIte, List.filter_cons, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        rw [ih _ rightLength, filter_gt_gt rest x cut h]

/-- Inserting a new root or moving an existing key to the root has the
same Cartesian description: split the old tree at the requested key. -/
def access (x : α) (tree : Tree α) : Tree α :=
  .node (below x tree) x (above x tree)

theorem access_cartesian (history : List α) (x : α) :
    access x (cartesian history) = cartesian (x :: history) := by
  simp [access,below_cartesian,above_cartesian]

end DynamicOptimality.Funnel.Warm
