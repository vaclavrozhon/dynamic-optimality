import DynamicOptimality.Funnel.QuotientPaths
import DynamicOptimality.Funnel.RunCompression
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Finset.Card

/-! # The foreign-prefix contribution is paid by the template and repeated runs -/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree ChaCha.ConvexSearchQuotient

theorem ancestors_nodup {α : Type*} [LinearOrder α] (tree : Tree α) (x : α)
    (ordered : Ordered tree) : (ancestors x tree).Nodup := by
  induction tree with
  | empty => simp [ancestors]
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases xa : x < a
    · simp only [ancestors,xa,↓reduceIte,List.nodup_cons]
      exact ⟨fun member => (lt_irrefl a) (left a (ancestors_mem member)),ihl ol⟩
    · by_cases ax : a < x
      · simp only [ancestors,xa,ax,↓reduceIte,List.nodup_cons]
        exact ⟨fun member => (lt_irrefl a) (right a (ancestors_mem member)),ihr orr⟩
      · simp [ancestors,xa,ax]

theorem project_ancestors_finset (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (ordered : Ordered tree) (x lo hi : Int)
    (lower : lo ≤ label x) (upper : label x ≤ hi)
    (range : ∀ q ∈ inorder tree, lo ≤ label q ∧ label q ≤ hi) :
    (ancestors (label x) (project label lo hi tree)).toFinset =
      ((foreignPrefix label x tree).map label).toFinset := by
  ext z
  simp only [List.mem_toFinset]
  constructor
  · intro member
    exact (project_ancestors_sublist label mono tree x lo hi lower upper).subset member
  · intro member
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp member
    have pathMem : q ∈ ancestors x tree := (List.takeWhile_sublist _).subset hq
    have bounds := range q (ancestors_mem pathMem)
    exact prefix_label_mem_project label mono tree ordered x lo hi lower upper hq bounds.1 bounds.2

theorem prefix_side_map (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (x : Int) :
    (((foreignPrefix label x tree).map label).map (fun z => decide (z < label x))) =
      (foreignPrefix label x tree).map (fun q => decide (q < x)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q member
  have foreign : label q ≠ label x := foreignPrefix_ne label x tree member
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,decide_eq_true_eq]
  constructor
  · intro strict
    by_contra failed
    have := mono (show x ≤ q by omega)
    omega
  · intro qx
    have := mono qx.le
    omega

theorem prefix_changes_bound (label : Int → Int) (mono : Monotone label)
    (tree : Tree Int) (ordered : Ordered tree) (x lo hi : Int)
    (lower : lo ≤ label x) (upper : label x ≤ hi)
    (range : ∀ q ∈ inorder tree, lo ≤ label q ∧ label q ≤ hi) :
    changes ((foreignPrefix label x tree).map (fun q => decide (q < x))) +
        2 * ((foreignPrefix label x tree).map label).toFinset.card ≤
      changes ((ancestors (label x) (project label lo hi tree)).map (fun z => decide (z < label x))) +
        2 * (runHeads ((foreignPrefix label x tree).map label)).length := by
  have nodup := ancestors_nodup (project label lo hi tree) (label x) (ordered_project label tree lo hi)
  have sublist := project_ancestors_sublist label mono tree x lo hi lower upper
  have bound := projection_changes_bound (fun z : Int => decide (z < label x)) nodup sublist
  have size : (ancestors (label x) (project label lo hi tree)).length =
      ((foreignPrefix label x tree).map label).toFinset.card := by
    rw [← List.toFinset_card_of_nodup nodup,project_ancestors_finset label mono tree ordered x lo hi lower upper range]
  simpa only [prefix_side_map label mono tree x,size] using bound

end DynamicOptimality.Funnel.Warm
