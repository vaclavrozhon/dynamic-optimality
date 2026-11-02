import DynamicOptimality.Funnel.WarmMTR

/-! # Restriction identities for split access

All algebraic identities concern the literal trees. Orderedness is used only
for the separate validity lemmas, not to replace any tree by an equal-cost
or equal-key surrogate.
-/

namespace DynamicOptimality.Funnel.ApproxMonotonicity

open ChaCha.MTR ChaCha.MTR.Tree Warm
variable {α : Type*} [LinearOrder α]

theorem below_nested (x y : α) (xy : x ≤ y) (tree : Tree α) :
    below x (below y tree) = below x tree := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    by_cases ax : a < x
    · have ay := ax.trans_le xy
      simp [below,ax,ay,ihl,ihr]
    · by_cases ay : a < y <;> simp [below,ax,ay,ihl]

theorem above_nested (x y : α) (xy : x ≤ y) (tree : Tree α) :
    above y (above x tree) = above y tree := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    by_cases ya : y < a
    · have xa := xy.trans_lt ya
      simp [above,xa,ya,ihl,ihr]
    · by_cases xa : x < a <;> simp [above,xa,ya,ihr]

theorem below_comm (x y : α) (tree : Tree α) :
    below x (below y tree) = below y (below x tree) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    by_cases ax : a < x <;> by_cases ay : a < y <;> simp [below,ax,ay,ihl,ihr]

theorem above_comm (x y : α) (tree : Tree α) :
    above x (above y tree) = above y (above x tree) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    by_cases xa : x < a <;> by_cases ya : y < a <;> simp [above,xa,ya,ihl,ihr]

theorem below_above_comm (x y : α) (yx : y < x) (tree : Tree α) :
    below x (above y tree) = above y (below x tree) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    by_cases ax : a < x <;> by_cases ya : y < a
    · simp [below,above,ax,ya,ihl,ihr]
    · simp [below,above,ax,ya,ihr]
    · simp [below,above,ax,ya,ihl]
    · exact False.elim ((not_lt_of_ge (le_of_not_gt ya)) (yx.trans_le (le_of_not_gt ax)))

theorem below_access (x y : α) (tree : Tree α) :
    below x (access y tree) = if y < x then access y (below x tree) else below x tree := by
  by_cases yx : y < x
  · simp [access,below,yx,below_comm x y tree,below_above_comm x y yx tree]
  · simp [access,below,yx,below_nested x y (le_of_not_gt yx) tree]

theorem above_access (x y : α) (tree : Tree α) :
    above x (access y tree) = if x < y then access y (above x tree) else above x tree := by
  by_cases xy : x < y
  · simp [access,above,xy,above_comm x y tree,← below_above_comm y x xy tree]
  · simp [access,above,xy,above_nested y x (le_of_not_gt xy) tree]

theorem inorder_below (cut : α) (tree : Tree α) (ordered : Ordered tree) :
    inorder (below cut tree) = (inorder tree).filter (fun z => decide (z < cut)) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases ac : a < cut
    · simp [below,ac,inorder,ihl ol,ihr orr,List.filter_append]
    · have noRight : (inorder r).filter (fun z => decide (z < cut)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hz
        simpa only [decide_eq_true_eq] using not_lt_of_ge ((le_of_not_gt ac).trans (right z hz).le)
      simp [below,ac,inorder,ihl ol,noRight,List.filter_append]

theorem inorder_above (cut : α) (tree : Tree α) (ordered : Ordered tree) :
    inorder (above cut tree) = (inorder tree).filter (fun z => decide (cut < z)) := by
  induction tree with
  | empty => rfl
  | node l a r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases ca : cut < a
    · simp [above,ca,inorder,ihl ol,ihr orr,List.filter_append]
    · have noLeft : (inorder l).filter (fun z => decide (cut < z)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hz
        simpa only [decide_eq_true_eq] using not_lt_of_ge ((left z hz).le.trans (le_of_not_gt ca))
      simp [above,ca,inorder,ihr orr,noLeft,List.filter_append]

theorem ordered_below (cut : α) (tree : Tree α) (ordered : Ordered tree) :
    Ordered (below cut tree) := by
  unfold Ordered
  rw [inorder_below cut tree ordered]
  exact ordered.filter _

theorem ordered_above (cut : α) (tree : Tree α) (ordered : Ordered tree) :
    Ordered (above cut tree) := by
  unfold Ordered
  rw [inorder_above cut tree ordered]
  exact ordered.filter _

theorem ordered_access (x : α) (tree : Tree α) (ordered : Ordered tree) :
    Ordered (access x tree) := by
  have ol := ordered_below x tree ordered
  have orr := ordered_above x tree ordered
  have left : ∀ z ∈ inorder (below x tree), z < x := by
    intro z hz
    rw [inorder_below x tree ordered] at hz
    exact of_decide_eq_true (List.mem_filter.mp hz).2
  have right : ∀ z ∈ inorder (above x tree), x < z := by
    intro z hz
    rw [inorder_above x tree ordered] at hz
    exact of_decide_eq_true (List.mem_filter.mp hz).2
  change ((inorder (below x tree) ++ [x]) ++ inorder (above x tree)).Pairwise (· < ·)
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨ol,by simp,?_⟩,orr,?_⟩
  · intro a ha b hb
    have same : b = x := by simpa using hb
    subst b
    exact left a ha
  · intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · exact (left a ha).trans (right b hb)
    · have same : a = x := by simpa using ha
      subst a
      exact right b hb

end DynamicOptimality.Funnel.ApproxMonotonicity
