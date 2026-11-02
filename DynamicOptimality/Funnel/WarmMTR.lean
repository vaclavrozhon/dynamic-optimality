import DynamicOptimality.Funnel.WarmRestriction

/-! # Warm access agrees with ordinary move-to-root

For an already present key, the split description of a warm access is exactly
the existing rotation-based `ChaCha.MTR.Tree.moveToRoot`. For an unseen key,
the same description inserts it at the root. This file introduces no second
paid BST execution model.
-/

namespace DynamicOptimality.Funnel.Warm

open ChaCha.MTR ChaCha.MTR.Tree

variable {α : Type*} [LinearOrder α]

theorem below_eq_self (cut : α) (tree : Tree α)
    (allBelow : ∀ y ∈ inorder tree, y < cut) : below cut tree = tree := by
  induction tree with
  | empty => rfl
  | node l y r ihl ihr =>
    have hy := allBelow y (by simp [inorder])
    have hl : ∀ z ∈ inorder l, z < cut := fun z hz => allBelow z (by simp [inorder,hz])
    have hr : ∀ z ∈ inorder r, z < cut := fun z hz => allBelow z (by simp [inorder,hz])
    simp only [below,hy,↓reduceIte,ihl hl,ihr hr]

theorem above_eq_self (cut : α) (tree : Tree α)
    (allAbove : ∀ y ∈ inorder tree, cut < y) : above cut tree = tree := by
  induction tree with
  | empty => rfl
  | node l y r ihl ihr =>
    have hy := allAbove y (by simp [inorder])
    have hl : ∀ z ∈ inorder l, cut < z := fun z hz => allAbove z (by simp [inorder,hz])
    have hr : ∀ z ∈ inorder r, cut < z := fun z hz => allAbove z (by simp [inorder,hz])
    simp only [above,hy,↓reduceIte,ihl hl,ihr hr]

theorem ordered_parts {l r : Tree α} {y : α} (ordered : Ordered (.node l y r)) :
    Ordered l ∧ Ordered r ∧ (∀ z ∈ inorder l, z < y) ∧ (∀ z ∈ inorder r, y < z) := by
  change ((inorder l ++ [y]) ++ inorder r).Pairwise (· < ·) at ordered
  obtain ⟨leftRoot,rightOrdered,cross⟩ := List.pairwise_append.mp ordered
  obtain ⟨leftOrdered,_,left⟩ := List.pairwise_append.mp leftRoot
  exact ⟨leftOrdered,rightOrdered,
    fun z hz => left z hz y (by simp),
    fun z hz => cross y (by simp) z hz⟩

theorem access_eq_moveToRoot (x : α) (tree : Tree α) (d : Nat)
    (ordered : Ordered tree) (success : searchDepth x tree = some d) :
    access x tree = moveToRoot x tree := by
  induction tree generalizing d with
  | empty => simp [searchDepth] at success
  | node l y r ihl ihr =>
    obtain ⟨ol,orr,left,right⟩ := ordered_parts ordered
    by_cases xy : x < y
    · simp only [searchDepth,xy,↓reduceIte] at success
      cases child : searchDepth x l with
      | none => simp [child] at success
      | some e =>
        have recurse :=  ihl e ol child
        have rightFixed : above x r = r :=
          above_eq_self x r (fun z hz => xy.trans (right z hz))
        simp only [access,below,above,not_lt_of_gt xy,xy,↓reduceIte,rightFixed]
        simp only [moveToRoot,xy,↓reduceIte,← recurse,access,rotateRight]
    · by_cases yx : y < x
      · simp only [searchDepth,xy,yx,↓reduceIte] at success
        cases child : searchDepth x r with
        | none => simp [child] at success
        | some e =>
          have recurse :=  ihr e orr child
          have leftFixed : below x l = l :=
            below_eq_self x l (fun z hz => (left z hz).trans yx)
          simp only [access,below,above,xy,yx,↓reduceIte,leftFixed]
          simp only [moveToRoot,xy,yx,↓reduceIte,← recurse,access,rotateLeft]
      · have same : x = y := le_antisymm (le_of_not_gt yx) (le_of_not_gt xy)
        subst y
        simp only [access,below,above,lt_self_iff_false,↓reduceIte,moveToRoot_root]
        rw [below_eq_self x l left,above_eq_self x r right]

/-- The warm Cartesian update performs exactly the existing MTR operation
whenever the requested key was already present. -/
theorem cartesian_cons_eq_moveToRoot (history : List α) (x : α) (d : Nat)
    (success : searchDepth x (cartesian history) = some d) :
    cartesian (x :: history) = moveToRoot x (cartesian history) := by
  rw [← access_cartesian]
  exact access_eq_moveToRoot x _ d (ordered_cartesian history) success

end DynamicOptimality.Funnel.Warm
