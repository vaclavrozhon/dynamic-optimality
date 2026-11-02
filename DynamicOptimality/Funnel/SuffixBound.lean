import DynamicOptimality.Funnel.QuotientPaths
import DynamicOptimality.Funnel.PathEndpoints
import DynamicOptimality.Funnel.UniformForeign
import Mathlib.Data.List.TakeWhile

/-! # The suffix after entering the own component

Convexity and the monotonicity of the two search spines force every foreign
suffix node onto one common side of the query. Its extra changes are therefore
paid by at most two units for every own-component run.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

def ownSuffix (label : Int → Int) (x : Int) (tree : Tree Int) : List Int :=
  (ancestors x tree).dropWhile (fun a => decide (label a ≠ label x))

theorem prefix_append_suffix (label : Int → Int) (x : Int) (tree : Tree Int) :
    foreignPrefix label x tree ++ ownSuffix label x tree = ancestors x tree := by
  exact List.takeWhile_append_dropWhile

private theorem left_tail_order (tree : Tree Int) (x r : Int) (ordered : Ordered tree)
    (before after : List Int) (split : before ++ r :: after = ancestors x tree)
    (rx : r < x) {q : Int} (member : q ∈ after) (qx : q < x) : r < q := by
  have pairs := left_ancestors_increasing tree x ordered
  rw [← split,List.filter_append] at pairs
  have tailPairs := (List.pairwise_append.mp pairs).2.1
  simp only [List.filter_cons,rx,decide_true,↓reduceIte] at tailPairs
  exact (List.pairwise_cons.mp tailPairs).1 q (List.mem_filter.mpr ⟨member,decide_eq_true qx⟩)

private theorem right_tail_order (tree : Tree Int) (x r : Int) (ordered : Ordered tree)
    (before after : List Int) (split : before ++ r :: after = ancestors x tree)
    (xr : x < r) {q : Int} (member : q ∈ after) (xq : x < q) : q < r := by
  have pairs := right_ancestors_decreasing tree x ordered
  rw [← split,List.filter_append] at pairs
  have tailPairs := (List.pairwise_append.mp pairs).2.1
  simp only [List.filter_cons,xr,decide_true,↓reduceIte] at tailPairs
  exact (List.pairwise_cons.mp tailPairs).1 q (List.mem_filter.mpr ⟨member,decide_eq_true xq⟩)

theorem suffix_uniform (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (x : Int) (ordered : Ordered tree) :
    ∃ foreign : Bool, ∀ q ∈ ownSuffix label x tree,
      decide (label q = label x) = false → decide (q < x) = foreign := by
  cases suffix : ownSuffix label x tree with
  | nil => exact ⟨false,by simp [suffix]⟩
  | cons r after =>
    have own : label r = label x := by
      have stopped := List.head?_dropWhile_not (fun a => decide (label a ≠ label x)) (ancestors x tree)
      have suffixEq : (ancestors x tree).dropWhile (fun a => decide (label a ≠ label x)) = r :: after := suffix
      rw [suffixEq] at stopped
      simpa only [List.head?_cons,decide_eq_false_iff_not,not_not] using stopped
    have split := prefix_append_suffix label x tree
    rw [suffix] at split
    have present : r ∈ ancestors x tree := by rw [← split]; simp
    have different : r ≠ x := fun equal => not_mem_ancestors tree x (equal ▸ present)
    rcases lt_or_gt_of_ne different with rx | xr
    · refine ⟨false,?_⟩
      intro q hq foreign
      have neq : label q ≠ label x := of_decide_eq_false foreign
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (neq own).elim
      · apply decide_eq_false
        intro qx
        have rq := left_tail_order tree x r ordered _ after split rx hq qx
        have lower := mono rq.le
        have upper := mono qx.le
        apply neq
        omega
    · refine ⟨true,?_⟩
      intro q hq foreign
      have neq : label q ≠ label x := of_decide_eq_false foreign
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (neq own).elim
      · apply decide_eq_true
        have notRight : ¬ x < q := by
          intro xq
          have qr := right_tail_order tree x r ordered _ after split xr hq xq
          have lower := mono xq.le
          have upper := mono qr.le
          apply neq
          omega
        have qDifferent : q ≠ x := fun equal => neq (congrArg label equal)
        omega

theorem suffix_own_filter (label : Int → Int) (tree : Tree Int) (x : Int) :
    (ownSuffix label x tree).filter (fun q => decide (label q = label x)) =
      (ancestors x tree).filter (fun q => decide (label q = label x)) := by
  have empty : (foreignPrefix label x tree).filter (fun q => decide (label q = label x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q member
    have foreign : label q ≠ label x := foreignPrefix_ne label x tree member
    simp [foreign]
  rw [← prefix_append_suffix label x tree,List.filter_append,empty,List.nil_append]

theorem suffix_changes_bound (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (x : Int) (ordered : Ordered tree) :
    changes ((ownSuffix label x tree).map (fun q => decide (q < x))) ≤
      changes (((ancestors x tree).filter (fun q => decide (label q = label x))).map
        (fun q => decide (q < x))) +
      2 * ownRuns (fun q => decide (label q = label x)) false (ownSuffix label x tree) := by
  obtain ⟨foreign,uniform⟩ := suffix_uniform label mono tree x ordered
  have bound := uniform_foreign_changes (fun q => decide (label q = label x))
    (fun q => decide (q < x)) foreign (ownSuffix label x tree) uniform
  simpa only [suffix_own_filter] using bound

end DynamicOptimality.Funnel.Warm
