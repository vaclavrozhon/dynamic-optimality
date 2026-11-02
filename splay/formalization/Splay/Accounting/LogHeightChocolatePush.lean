import Splay.Accounting.LogHeightChocolateGeometry

namespace Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate

open Splay.Tree OfflineNormalForm

namespace Chocolate

/-- Number of currently active levels; frozen levels do not participate in
a carry until a later pop explicitly defrosts them. -/
def activeDepth : {kind : Bool} → {level lower upper : ℕ} → {tree : BST lower upper} →
    Chocolate kind level tree → ℕ
  | _, _, _, _, _, .base _ => 0
  | _, _, _, _, _, .oneEnd _ _ => 1
  | _, _, _, _, _, .twoEnd _ _ _ => 1
  | _, _, _, _, _, .threeEnd _ _ _ _ => 1
  | _, _, _, _, _, .oneNext _ layer _ _ => layer.activeDepth + 1
  | _, _, _, _, _, .twoNext _ _ layer _ _ => layer.activeDepth + 1
  | _, _, _, _, _, .threeNext _ _ _ layer _ _ => layer.activeDepth + 1
  | _, _, _, _, _, .icingBase _ => 0
  | _, _, _, _, _, .freezeCrumb _ _ _ => 0
  | _, _, _, _, _, .freezeLayer _ _ _ _ _ => 0

theorem mass_eq_of_interval {lower upper : ℕ} (a b : BST lower upper) : mass a = mass b := by
  have left := a.size_add_lower_eq_upper
  have right := b.size_add_lower_eq_upper
  dsimp [mass]
  omega

/-- Push an arbitrary weighted crumb at the minimum end. The path is made
of ordinary rotations, and its connected support is covered by the same
counter potential as its rotation count. -/
theorem exists_push {level lower root upper : ℕ}
    {incoming : BST lower root} {before : BST (root + 1) upper}
    (layer : Layer level before) (crumb : Crumb level incoming) :
    ∃ (after : BST lower upper) (result : Layer level after) (cost : ℕ),
      result.selected.frontier = crumb.selected.frontier.append layer.selected.frontier ∧
      HasSupportedPath (.node incoming before) after cost cost ∧
      cost + 16 * result.potential ≤ 16 * layer.potential + 16 ∧
      cost ≤ 16 * (layer.activeDepth + 1) := by
  generalize sizeEq : before.size = count
  induction count using Nat.strong_induction_on generalizing level lower root upper with
  | h count ih =>
      cases layer with
      | base old =>
          refine ⟨_, .oneEnd crumb (.icingBase old), 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | oneEnd first icing =>
          refine ⟨_, .twoEnd crumb first icing, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | twoEnd first second icing =>
          refine ⟨_, .threeEnd crumb first second icing, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | @threeEnd _ _ k0 k1 k2 _ a b c icingTree first second third icing =>
          let merged : Crumb (level + 1) (.node b c) := .join second third
          have path := ((HasSupportedPath.rootLeft b c icingTree).rightContext a).rightContext incoming
          by_cases thick : mass icingTree ≤ mass (.node b c)
          · let result : Layer level (.node incoming (.node a (.node (.node b c) icingTree))) :=
              .twoEnd crumb first (.freezeCrumb merged icing thick)
            refine ⟨_, result, 4, ?_, path.mono (by omega) (by omega), ?_, ?_⟩
            · simp [result, selected, merged, Crumb.selected, RootPrefix.frontier,
                SupportFrontier.append_assoc]
            · simp only [result, potential]; omega
            · simp [activeDepth]
          · let result : Layer level (.node incoming (.node a (.node (.node b c) icingTree))) :=
              .twoNext crumb first (.base merged) icing (by omega)
            refine ⟨_, result, 4, ?_, path.mono (by omega) (by omega), ?_, ?_⟩
            · simp [result, selected, merged, Crumb.selected, RootPrefix.frontier,
                SupportFrontier.append_assoc]
            · simp only [result, potential]; omega
            · simp [activeDepth]
      | oneNext first next icing thin =>
          refine ⟨_, .twoNext crumb first next icing thin, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | twoNext first second next icing thin =>
          refine ⟨_, .threeNext crumb first second next icing thin, 0, rfl, .refl _, ?_, ?_⟩ <;>
            simp [potential, activeDepth] <;> omega
      | @threeNext _ _ k0 k1 k2 pivot _ a b c nextTree icingTree first second third next icing thin =>
          let merged : Crumb (level + 1) (.node b c) := .join second third
          have firstPath := ((HasSupportedPath.rootLeft b c (.node nextTree icingTree)).rightContext a).rightContext incoming
          have secondPath := ((HasSupportedPath.rootLeft (.node b c) nextTree icingTree).rightContext a).rightContext incoming
          have path := firstPath.trans secondPath
          by_cases thick : mass icingTree ≤ mass (.node (.node b c) nextTree)
          · let result : Layer level (.node incoming (.node a (.node (.node (.node b c) nextTree) icingTree))) :=
              .twoEnd crumb first (.freezeLayer merged next icing thin thick)
            refine ⟨_, result, 8, ?_, path.mono (by omega) (by omega), ?_, ?_⟩
            · simp [result, selected, merged, Crumb.selected, RootPrefix.frontier,
                SupportFrontier.append_assoc]
            · simp only [result, potential]; omega
            · simp only [activeDepth]; omega
          · obtain ⟨newTree, newLayer, childCost, frontier, childPath, amortized, worst⟩ :=
              ih nextTree.size (by simp only [BST.size] at sizeEq; omega) next merged rfl
            have sameMass := mass_eq_of_interval newTree (.node (.node b c) nextTree)
            let result : Layer level (.node incoming (.node a (.node newTree icingTree))) :=
              .twoNext crumb first newLayer icing (by omega)
            have finish := ((childPath.leftContext icingTree).rightContext a).rightContext incoming
            refine ⟨_, result, childCost + 11, ?_, (path.trans finish).mono (by omega) (by omega), ?_, ?_⟩
            · simp only [result, selected, RootPrefix.frontier]
              rw [frontier]
              simp [merged, Crumb.selected, RootPrefix.frontier, SupportFrontier.append_assoc]
            · simp only [result, potential] at *; omega
            · simp only [activeDepth]; omega

end Chocolate

end Splay.Accounting.OfflineConnectedSupport.LogHeightChocolate
