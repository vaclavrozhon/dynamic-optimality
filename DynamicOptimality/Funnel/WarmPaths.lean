import DynamicOptimality.Funnel.WarmMTR
import DynamicOptimality.Funnel.PastList
import DynamicOptimality.Funnel.ConvexVisibility

/-! # The ordered search-path invariants for convex composition -/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem past_nodup (history : List α) (x : α) : (past x history).Nodup := by
  induction history with
  | nil => simp [past]
  | cons a history ih =>
    by_cases same : a = x
    · simp [past,same]
    · simp only [past,same,↓reduceIte,List.nodup_cons]
      constructor
      · intro member
        have outside := of_decide_eq_true (List.mem_filter.mp member).2
        exact outside (between_left _ _)
      · exact ih.filter _

theorem past_sublist (history : List α) (x : α) : (past x history).Sublist history := by
  induction history with
  | nil => simp [past]
  | cons a history ih =>
    by_cases same : a = x
    · simp [past,same]
    · simp only [past,same,↓reduceIte]
      exact (List.filter_sublist.trans ih).cons_cons _

theorem ancestors_cartesian_nodup (history : List α) (x : α) :
    (ancestors x (cartesian history)).Nodup := by
  rw [ancestors_eq_past]
  exact past_nodup history x

theorem ancestors_cartesian_sublist (history : List α) (x : α) :
    (ancestors x (cartesian history)).Sublist history := by
  rw [ancestors_eq_past]
  exact past_sublist history x

/-- The component search is exactly the own-component subsequence of the
physical search, preserving the complete order of proper ancestors. -/
theorem convex_ancestors_eq_filter (history : List α) (label : α → β)
    (mono : Monotone label) (x : α) :
    ancestors x (cartesian (history.filter (fun y => decide (label y = label x)))) =
      (ancestors x (cartesian history)).filter (fun y => decide (label y = label x)) := by
  rw [ancestors_eq_past,ancestors_eq_past]
  apply past_filter
  · simp
  · intro q a hq between
    apply decide_eq_true
    have same : label q = label x := of_decide_eq_true hq
    exact (same_label_between label mono same between).trans same

theorem ancestors_mem {tree : Tree α} {x q : α} (member : q ∈ ancestors x tree) :
    q ∈ inorder tree := by
  induction tree with
  | empty => simp [ancestors] at member
  | node l a r ihl ihr =>
    by_cases xa : x < a
    · simp only [ancestors,xa,↓reduceIte,List.mem_cons] at member
      rcases member with rfl | member
      · simp [inorder]
      · have := ihl member
        simp [inorder,this]
    · by_cases ax : a < x
      · simp only [ancestors,xa,ax,↓reduceIte,List.mem_cons] at member
        rcases member with rfl | member
        · simp [inorder]
        · have := ihr member
          simp [inorder,this]
      · simp [ancestors,xa,ax] at member

/-- On the left side of a search, keys increase toward the query. -/
theorem left_ancestors_increasing (tree : Tree α) (x : α) (ordered : Ordered tree) :
    ((ancestors x tree).filter (fun q => decide (q < x))).Pairwise (· < ·) := by
  induction tree with
  | empty => simp [ancestors]
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,_,right⟩ := ordered_parts ordered
    by_cases xa : x < a
    · simpa [ancestors,xa,not_lt_of_gt xa] using ihl ol
    · by_cases ax : a < x
      · simp only [ancestors,xa,ax,↓reduceIte,List.filter_cons,decide_true,↓reduceIte,List.pairwise_cons]
        refine ⟨?_,ihr orr⟩
        intro q member
        exact right q (ancestors_mem (List.mem_filter.mp member).1)
      · simp [ancestors,xa,ax]

/-- On the right side of a search, keys decrease toward the query. -/
theorem right_ancestors_decreasing (tree : Tree α) (x : α) (ordered : Ordered tree) :
    ((ancestors x tree).filter (fun q => decide (x < q))).Pairwise (· > ·) := by
  induction tree with
  | empty => simp [ancestors]
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,_⟩ := ordered_parts ordered
    by_cases xa : x < a
    · simp only [ancestors,xa,↓reduceIte,List.filter_cons,decide_true,↓reduceIte,List.pairwise_cons]
      refine ⟨?_,ihl ol⟩
      intro q member
      exact left q (ancestors_mem (List.mem_filter.mp member).1)
    · by_cases ax : a < x
      · simpa [ancestors,xa,ax] using ihr orr
      · simp [ancestors,xa,ax]

end DynamicOptimality.Funnel.Warm
