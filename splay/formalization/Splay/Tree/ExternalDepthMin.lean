import Splay.Tree.DepthMin
import Splay.Tree.External

namespace Splay.Tree

/--
Every nonempty closed interval of value/null positions has a unique
minimum-depth external node.

This is the direct formal counterpart of `lemma:unique-depth-minimum`.
-/
theorem BST.existsUnique_intervalExternalDepthMin
    {treeLower treeUpper : ℕ} (tree : BST treeLower treeUpper)
    {intervalLower intervalUpper : ℕ}
    (hInsideLower : 2 * treeLower ≤ intervalLower)
    (hNonempty : intervalLower ≤ intervalUpper)
    (hInsideUpper : intervalUpper ≤ 2 * treeUpper) :
    ∃! position,
      IsIntervalMin (BST.externalDepth tree)
        intervalLower intervalUpper position := by
  induction tree generalizing intervalLower intervalUpper with
  | empty boundary =>
      refine ⟨2 * boundary, ⟨by omega, by omega, ?_⟩, ?_⟩
      · intro position _ _
        simp [BST.externalDepth]
      · intro position hPosition
        have hPositionLower := hPosition.1
        have hPositionUpper := hPosition.2.1
        omega
  | @node treeLower root treeUpper left right ihLeft ihRight =>
      by_cases hLeft : intervalUpper < 2 * root + 1
      · have hDepthEqual :
            ∀ position, intervalLower ≤ position → position ≤ intervalUpper →
              BST.externalDepth (.node left right) position =
                (BST.externalDepth left position).succ := by
          intro position _ hPositionUpper
          exact BST.externalDepth_node_of_lt_root left right (by omega)
        have hMinIff :
            ∀ position,
              IsIntervalMin (BST.externalDepth (.node left right))
                  intervalLower intervalUpper position ↔
                IsIntervalMin (BST.externalDepth left)
                  intervalLower intervalUpper position := by
          intro position
          exact (isIntervalMin_congrOn hDepthEqual).trans
            isIntervalMin_succ_iff
        obtain ⟨position, hPositionMin, hPositionUnique⟩ :=
          ihLeft hInsideLower hNonempty (by omega)
        refine ⟨position, (hMinIff position).2 hPositionMin, ?_⟩
        intro other hOther
        exact hPositionUnique other ((hMinIff other).1 hOther)
      · by_cases hRight : 2 * root + 1 < intervalLower
        · have hDepthEqual :
              ∀ position, intervalLower ≤ position → position ≤ intervalUpper →
                BST.externalDepth (.node left right) position =
                  (BST.externalDepth right position).succ := by
            intro position hPositionLower _
            exact BST.externalDepth_node_of_root_lt left right (by omega)
          have hMinIff :
              ∀ position,
                IsIntervalMin (BST.externalDepth (.node left right))
                    intervalLower intervalUpper position ↔
                  IsIntervalMin (BST.externalDepth right)
                    intervalLower intervalUpper position := by
            intro position
            exact (isIntervalMin_congrOn hDepthEqual).trans
              isIntervalMin_succ_iff
          obtain ⟨position, hPositionMin, hPositionUnique⟩ :=
            ihRight (by omega) hNonempty hInsideUpper
          refine ⟨position, (hMinIff position).2 hPositionMin, ?_⟩
          intro other hOther
          exact hPositionUnique other ((hMinIff other).1 hOther)
        · have hRootLower : intervalLower ≤ 2 * root + 1 := by omega
          have hRootUpper : 2 * root + 1 ≤ intervalUpper := by omega
          refine ⟨2 * root + 1, ⟨hRootLower, hRootUpper, ?_⟩, ?_⟩
          · intro position _ _
            simp [BST.externalDepth]
          · intro position hPositionMin
            by_contra hPositionNe
            have hDepthPositive :
                0 < BST.externalDepth (.node left right) position := by
              by_cases hPositionLeft : position < 2 * root + 1
              · simp [BST.externalDepth, hPositionLeft]
              · simp [BST.externalDepth, hPositionLeft, hPositionNe]
            have hDepthAtMostRoot :=
              hPositionMin.2.2 (2 * root + 1) hRootLower hRootUpper
            simp only [BST.externalDepth_root] at hDepthAtMostRoot
            omega

end Splay.Tree
