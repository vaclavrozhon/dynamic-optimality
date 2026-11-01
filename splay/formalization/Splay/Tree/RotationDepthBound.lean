import Splay.Tree.RotationDepth

namespace Splay.Tree.BST.RotationAt

/--
A single rotation, at any contextual depth, changes the depth of every
external inorder position by at most one.

This is the context-closed form of the three exact root-rotation sector
lemmas.  It is stated without truncated subtraction, as two natural-number
inequalities.
-/
theorem externalDepth_within_one
    {depth lower upper : ℕ}
    {before after : BST lower upper}
    (step : RotationAt depth before after)
    (position : ℕ) :
    externalDepth after position ≤ externalDepth before position + 1 ∧
      externalDepth before position ≤ externalDepth after position + 1 := by
  induction step with
  | root rootStep =>
      cases rootStep with
      | right a b c =>
          rename_i _ _ promoted demoted
          by_cases hPromoted : position ≤ 2 * promoted + 1
          · have hDepth :=
              RootRotation.right_externalDepth_promotedSector
                (promoted := promoted) (demoted := demoted)
                (position := position) a b c hPromoted
            omega
          · by_cases hMiddle : position < 2 * demoted + 1
            · have hDepth :=
              RootRotation.right_externalDepth_middleSector
                  (promoted := promoted) (demoted := demoted)
                  (position := position) a b c (by omega) hMiddle
              omega
            · have hDepth :=
              RootRotation.right_externalDepth_demotedSector
                  (promoted := promoted) (demoted := demoted)
                  (position := position) a b c (by omega)
              omega
      | left a b c =>
          rename_i _ _ demoted promoted
          by_cases hDemoted : position ≤ 2 * demoted + 1
          · have hDepth :=
              RootRotation.left_externalDepth_demotedSector
                (demoted := demoted) (promoted := promoted)
                (position := position) a b c hDemoted
            omega
          · by_cases hMiddle : position < 2 * promoted + 1
            · have hDepth :=
              RootRotation.left_externalDepth_middleSector
                  (demoted := demoted) (promoted := promoted)
                  (position := position) a b c (by omega) hMiddle
              omega
            · have hDepth :=
              RootRotation.left_externalDepth_promotedSector
                  (demoted := demoted) (promoted := promoted)
                  (position := position) a b c (by omega)
              omega
  | @leftContext depth lower root upper before after step right ih =>
      by_cases hLeft : position < 2 * root + 1
      · rw [externalDepth_node_of_lt_root before right hLeft,
            externalDepth_node_of_lt_root after right hLeft]
        omega
      · by_cases hRoot : position = 2 * root + 1
        · subst position
          simp
        · have hRight : 2 * root + 1 < position := by omega
          rw [externalDepth_node_of_root_lt before right hRight,
              externalDepth_node_of_root_lt after right hRight]
          omega
  | @rightContext depth lower root upper left before after step ih =>
      by_cases hLeft : position < 2 * root + 1
      · rw [externalDepth_node_of_lt_root left before hLeft,
            externalDepth_node_of_lt_root left after hLeft]
        omega
      · by_cases hRoot : position = 2 * root + 1
        · subst position
          simp
        · have hRight : 2 * root + 1 < position := by omega
          rw [externalDepth_node_of_root_lt left before hRight,
              externalDepth_node_of_root_lt left after hRight]
          omega

/--
Integer reformulation: the signed rank shift of an external position under
one contextual rotation belongs to `{-1, 0, 1}`.
-/
theorem exists_signedShift
    {depth lower upper : ℕ}
    {before after : BST lower upper}
    (step : RotationAt depth before after)
    (position : ℕ) :
    ∃ shift : ℤ,
      (shift = -1 ∨ shift = 0 ∨ shift = 1) ∧
        (externalDepth after position : ℤ) =
          (externalDepth before position : ℤ) + shift := by
  have hBound := step.externalDepth_within_one position
  by_cases hDecrease :
      externalDepth after position < externalDepth before position
  · refine ⟨-1, Or.inl rfl, ?_⟩
    omega
  · by_cases hIncrease :
        externalDepth before position < externalDepth after position
    · refine ⟨1, Or.inr (Or.inr rfl), ?_⟩
      omega
    · refine ⟨0, Or.inr (Or.inl rfl), ?_⟩
      omega

end Splay.Tree.BST.RotationAt
