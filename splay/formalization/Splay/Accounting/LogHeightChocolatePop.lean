import Splay.Accounting.LogHeightChocolatePush

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

namespace Chocolate

theorem eq_base_of_activeDepth_zero {level lower upper : ℕ} {tree : BST lower upper}
    (layer : Layer level tree) (zero : layer.activeDepth = 0) :
    ∃ crumb : Crumb level tree, layer = .base crumb := by
  cases layer with
  | base crumb => exact ⟨crumb, rfl⟩
  | oneEnd => simp [activeDepth] at zero
  | twoEnd => simp [activeDepth] at zero
  | threeEnd => simp [activeDepth] at zero
  | oneNext => simp [activeDepth] at zero
  | twoNext => simp [activeDepth] at zero
  | threeNext => simp [activeDepth] at zero

/-- Defrost at most one icing element. Its stored old layer is reinstated
literally, and its potential is unchanged. -/
theorem exists_defrost {level lower upper : ℕ} {before : BST lower upper}
    (icing : Icing level before) :
    ∃ (after : BST lower upper) (result : Layer level after) (cost : ℕ),
      result.selected.frontier = icing.selected.frontier ∧
      HasSupportedPath before after cost cost ∧ result.potential = icing.potential ∧ cost ≤ 4 := by
  cases icing with
  | icingBase crumb => exact ⟨_, .base crumb, 0, rfl, .refl _, rfl, by decide⟩
  | @freezeCrumb level lower root upper crumbTree icingTree crumb tail thick =>
      cases crumb with
      | @join level lower root upper left right a b =>
          refine ⟨_, .twoEnd a b tail, 2, ?_, (HasSupportedPath.rootRight left right icingTree).mono (by omega) (by omega), rfl, by decide⟩
          simp [selected, Crumb.selected, RootPrefix.frontier, SupportFrontier.append_assoc]
  | @freezeLayer level lower first second upper crumbTree nextTree icingTree crumb next tail thin thick =>
      cases crumb with
      | @join level lower root upper left right a b =>
          have firstPath := HasSupportedPath.rootRight (.node left right) nextTree icingTree
          have secondPath := HasSupportedPath.rootRight left right (.node nextTree icingTree)
          refine ⟨_, .twoNext a b next tail thin, 4, ?_, (firstPath.trans secondPath).mono (by omega) (by omega), rfl, by decide⟩
          simp [selected, Crumb.selected, RootPrefix.frontier, SupportFrontier.append_assoc]

/-- Remove the first regular crumb, restoring the same weighted invariants
by ordinary rotations. Frozen fragments require only constant work; a borrow
that continues to the next layer releases one unit of potential. -/
theorem exists_pop {level lower upper : ℕ} {before : BST lower upper}
    (layer : Layer level before) (positive : 0 < layer.activeDepth) :
    ∃ (root : ℕ) (first : BST lower root) (firstCrumb : Crumb level first)
      (after : BST (root + 1) upper) (result : Layer level after) (cost : ℕ),
      layer.selected.frontier = firstCrumb.selected.frontier.append result.selected.frontier ∧
      HasSupportedPath before (.node first after) cost cost ∧
      cost + 16 * result.potential ≤ 16 * layer.potential + 16 ∧
      cost ≤ 16 * (layer.activeDepth + 1) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing level lower upper with
  | h count ih =>
      cases layer with
      | base crumb => simp [activeDepth] at positive
      | @oneEnd _ _ root _ a icingTree first icing =>
          obtain ⟨after, result, cost, frontier, path, potentialEq, bound⟩ := icing.exists_defrost
          refine ⟨_, a, first, after, result, cost + 1, ?_,
            (path.rightContext a).mono (by omega) (by omega), ?_, ?_⟩
          · simp only [selected, RootPrefix.frontier, frontier]
          · simp only [potential]; omega
          · simp only [activeDepth]; omega
      | twoEnd first second icing =>
          refine ⟨_, _, first, _, .oneEnd second icing, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | threeEnd first second third icing =>
          refine ⟨_, _, first, _, .twoEnd second third icing, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | @oneNext _ _ root pivot _ a nextTree icingTree first next icing thin =>
          by_cases active : 0 < next.activeDepth
          · obtain ⟨split, chunk, merged, restTree, rest, childCost, frontier, childPath, amortized, worst⟩ :=
              ih nextTree.size (by simp only [BST.size] at sizeEq; omega) next active rfl
            have massEq := mass_eq_of_interval nextTree (.node chunk restTree)
            have restThin : mass restTree < mass icingTree := by
              simp only [mass, BST.size] at massEq thin ⊢
              omega
            cases merged with
            | @join level lower middle upper left right b c =>
                have expose := (childPath.leftContext icingTree).rightContext a
                have rotateOne := (HasSupportedPath.rootRight (.node left right) restTree icingTree).rightContext a
                have rotateTwo := (HasSupportedPath.rootRight left right (.node restTree icingTree)).rightContext a
                let result : Layer level (.node left (.node right (.node restTree icingTree))) :=
                  .twoNext b c rest icing restThin
                refine ⟨_, a, first, _, result, childCost + 8, ?_,
                  ((expose.trans rotateOne).trans rotateTwo).mono (by omega) (by omega), ?_, ?_⟩
                · simp only [selected, RootPrefix.frontier]
                  rw [frontier]
                  simp [result, selected, Crumb.selected, RootPrefix.frontier,
                    SupportFrontier.append_assoc]
                · simp only [result, potential]; omega
                · simp only [activeDepth]; omega
          · obtain ⟨merged, same⟩ := next.eq_base_of_activeDepth_zero (by omega)
            cases same
            cases merged with
            | @join level lower middle upper left right b c =>
                refine ⟨_, a, first, _, .twoEnd b c icing, 3, ?_,
                  ((HasSupportedPath.rootRight left right icingTree).rightContext a).mono
                    (by omega) (by omega), ?_, ?_⟩
                · simp [selected, Crumb.selected, RootPrefix.frontier, SupportFrontier.append_assoc]
                · simp only [potential]; omega
                · simp [activeDepth]
      | twoNext first second next icing thin =>
          refine ⟨_, _, first, _, .oneNext second next icing thin, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | threeNext first second third next icing thin =>
          refine ⟨_, _, first, _, .twoNext second third next icing thin, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega

end Chocolate

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
