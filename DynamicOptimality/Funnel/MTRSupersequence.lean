import ChaCha.BSTExecution
import ChaCha.ExecutionFacts
import DynamicOptimality.Funnel.WarmMTR
import DynamicOptimality.ConnectedPointer

/-! # Generic-key MTR supersequences for the shared BST optimum

The existing three-key MTR table and marked-rotation simulation suffice here;
ambient preference normalization and a Boolean-key encoding are unnecessary.
The original access word is retained and the physical initial tree is restored.
-/

namespace DynamicOptimality.Funnel.MTRSimulation

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

private theorem ordered_left {l r : ChaCha.MTR.Tree α} {x : α} (h : Ordered (.node l x r)) :
    Ordered l := (Warm.ordered_parts h).1

private theorem ordered_right {l r : ChaCha.MTR.Tree α} {x : α} (h : Ordered (.node l x r)) :
    Ordered r := (Warm.ordered_parts h).2.1

private theorem ordered_left_lt {l r : ChaCha.MTR.Tree α} {x y : α}
    (h : Ordered (.node l x r)) (hy : y ∈ inorder l) : y < x :=
  (Warm.ordered_parts h).2.2.1 y hy

private theorem ordered_lt_right {l r : ChaCha.MTR.Tree α} {x y : α}
    (h : Ordered (.node l x r)) (hy : y ∈ inorder r) : x < y :=
  (Warm.ordered_parts h).2.2.2 y hy

private theorem ordered_hull_keys {a b c : α} {A B C D : ChaCha.MTR.Tree α} (s : Shape3)
    (h : Ordered (hull3 a b c A B C D s)) : a < b ∧ b < c := by
  cases s with
  | t1 => exact ⟨ordered_lt_right h (by simp [inorder]),
      ordered_lt_right (ordered_right h) (by simp [inorder])⟩
  | t2 => exact ⟨ordered_lt_right h (by simp [inorder]),
      ordered_left_lt (ordered_right h) (by simp [inorder])⟩
  | t3 => exact ⟨ordered_left_lt h (by simp [inorder]), ordered_lt_right h (by simp [inorder])⟩
  | t4 => exact ⟨ordered_lt_right (ordered_left h) (by simp [inorder]),
      ordered_left_lt h (by simp [inorder])⟩
  | t5 => exact ⟨ordered_left_lt (ordered_left h) (by simp [inorder]),
      ordered_left_lt h (by simp [inorder])⟩

private theorem hull_successful {a b c : α} (A B C D : ChaCha.MTR.Tree α) (ab : a < b) (bc : b < c)
    (s : Shape3) (qs : List (Fin 3)) :
    Successful (hull3 a b c A B C D s) (qs.map (key3 a b c)) := by
  induction qs generalizing s with
  | nil => trivial
  | cons q qs ih =>
    constructor
    · exact ⟨shapeDepth s q,searchDepth_hull3 a b c A B C D ab bc s q⟩
    · rw [moveToRoot_hull3 a b c A B C D ab bc s q]
      exact ih (nextShape s q)

private theorem hull_simulation {a b c : α} (A B C D : ChaCha.MTR.Tree α) (s t : Shape3)
    (ordered : Ordered (hull3 a b c A B C D s)) :
    ∃ qs : List α, run (hull3 a b c A B C D s) qs = hull3 a b c A B C D t ∧
      runCost (hull3 a b c A B C D s) qs ≤ 15 ∧ Successful (hull3 a b c A B C D s) qs := by
  obtain ⟨ab,bc⟩ := ordered_hull_keys s ordered
  obtain ⟨qs,_,endpoint,_,cost⟩ := three_key_simulation a b c A B C D ab bc .rightSplit s t
  exact ⟨qs.map (key3 a b c),endpoint,cost,hull_successful A B C D ab bc s qs⟩

theorem restricted_simulation {t u : ChaCha.MTR.Tree α} (step : RestrictedStep t u) (ordered : Ordered t) :
    ∃ qs : List α, run t qs = u ∧ runCost t qs ≤ 15 ∧ Successful t qs := by
  cases step with
  | rootRight A B C a b =>
    have ab : a < b := ordered_left_lt ordered (by simp [inorder])
    refine ⟨[a],?_,?_,?_⟩
    · simp [run,moveToRoot,ab,rotateRight]
    · simp [runCost,searchDepth,ab]
    · exact ⟨⟨1,by simp [searchDepth,ab]⟩,trivial⟩
  | rootLeft A B C a b =>
    have ab : a < b := ordered_lt_right ordered (by simp [inorder])
    refine ⟨[b],?_,?_,?_⟩
    · simp [run,moveToRoot,ab,not_lt_of_gt ab,rotateLeft]
    · simp [runCost,searchDepth,ab,not_lt_of_gt ab]
    · exact ⟨⟨1,by simp [searchDepth,ab,not_lt_of_gt ab]⟩,trivial⟩
  | rightRight A B C D a b c => exact hull_simulation A B C D .t2 .t1 ordered
  | rightLeft A B C D a b c => exact hull_simulation A B C D .t1 .t2 ordered
  | leftRight A B C D a b c => exact hull_simulation A B C D .t5 .t4 ordered
  | leftLeft A B C D a b c => exact hull_simulation A B C D .t4 .t5 ordered

theorem marked_simulation {t u : ChaCha.MTR.Tree α} {xs : List α} {k : Nat}
    (trace : MarkedTrace t xs u k) (ordered : Ordered t) :
    ∃ zs : List α, xs.Sublist zs ∧ run t zs = u ∧
      runCost t zs ≤ 15*k + xs.length ∧ Successful t zs := by
  induction trace with
  | nil t => exact ⟨[],.refl _,rfl,by simp [runCost],trivial⟩
  | @rotate t u v xs k step rest ih =>
    have nextOrdered : Ordered u := by unfold Ordered; rw [← step.inorder_eq]; exact ordered
    obtain ⟨qs,endpoint,cost,success⟩ := restricted_simulation step ordered
    obtain ⟨rs,sublist,final,tailCost,tailSuccess⟩ := ih nextOrdered
    refine ⟨qs ++ rs,sublist.trans (List.sublist_append_right _ _),?_,?_,?_⟩
    · rw [run_append,endpoint,final]
    · rw [runCost_append,endpoint]
      omega
    · exact (successful_append t qs rs).mpr ⟨success,endpoint.symm ▸ tailSuccess⟩
  | @serve t v x xs k atRoot rest ih =>
    obtain ⟨rs,sublist,endpoint,cost,success⟩ := ih ordered
    have unchanged : moveToRoot x t = t := by
      cases t with
      | empty => simp [rootKey] at atRoot
      | node l a r =>
        simp only [rootKey,Option.some.injEq] at atRoot
        subst a
        exact moveToRoot_root l r x
    have depth : searchDepth x t = some 0 := by
      cases t with
      | empty => simp [rootKey] at atRoot
      | node l a r =>
        simp only [rootKey,Option.some.injEq] at atRoot
        subst a
        exact searchDepth_root l r x
    refine ⟨x :: rs,sublist.cons_cons x,?_,?_,?_⟩
    · simpa only [run,List.foldl_cons,unchanged] using endpoint
    · simp only [runCost,depth,Option.getD_some,Nat.zero_add,unchanged,List.length_cons]
      omega
    · exact ⟨⟨0,depth⟩,unchanged.symm ▸ success⟩

theorem closed_supersequence {t u : ChaCha.MTR.Tree α} {xs : List α} {cost : Nat}
    (execution : AccessExecution t xs u cost) (ordered : Ordered t) :
    ∃ zs : List α, xs.Sublist zs ∧ run t zs = t ∧ runCost t zs ≤ 361*cost ∧ Successful t zs := by
  obtain ⟨k,bound,trace⟩ := execution.closed_marked_trace ordered
  obtain ⟨zs,sublist,endpoint,costBound,success⟩ := marked_simulation trace ordered
  have length := execution.length_le_cost
  exact ⟨zs,sublist,endpoint,by omega,success⟩

/-- No startup term is needed: the source tree is the attained optimum's tree. -/
theorem shared_OPT_supersequence {n : Nat} (word : List (Fin n)) :
    ∃ (tree : ChaCha.MTR.Tree Nat) (expanded : List Nat),
      (word.map Fin.val).Sublist expanded ∧ run tree expanded = tree ∧
      runCost tree expanded ≤ 13357 * DynamicOptimality.OPT word ∧ Successful tree expanded := by
  obtain ⟨initial,final,cost,execution,bound⟩ := DynamicOptimality.exists_pointer_of_OPT word
  obtain ⟨hullCost,hullBound,hull⟩ := execution.toAccessExecution
  obtain ⟨expanded,sublist,endpoint,expandedCost,success⟩ :=
    closed_supersequence hull initial.toRaw_ordered
  exact ⟨initial.toRaw,expanded,sublist,endpoint,by omega,success⟩

end DynamicOptimality.Funnel.MTRSimulation
