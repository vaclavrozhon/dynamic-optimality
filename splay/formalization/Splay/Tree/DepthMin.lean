import Splay.Tree.Basic
import Mathlib.Logic.ExistsUnique

namespace Splay.Tree

/-- A candidate is a minimum of `rank` on the closed interval `[lower, upper]`. -/
def IsIntervalMin (rank : ℕ → ℕ) (lower upper candidate : ℕ) : Prop :=
  lower ≤ candidate ∧ candidate ≤ upper ∧
    ∀ key, lower ≤ key → key ≤ upper → rank candidate ≤ rank key

theorem isIntervalMin_congrOn {rank₁ rank₂ : ℕ → ℕ}
    {lower upper candidate : ℕ}
    (hEqual : ∀ key, lower ≤ key → key ≤ upper → rank₁ key = rank₂ key) :
    IsIntervalMin rank₁ lower upper candidate ↔
      IsIntervalMin rank₂ lower upper candidate := by
  constructor
  · rintro ⟨hLower, hUpper, hMin⟩
    refine ⟨hLower, hUpper, ?_⟩
    intro key hKeyLower hKeyUpper
    rw [← hEqual candidate hLower hUpper, ← hEqual key hKeyLower hKeyUpper]
    exact hMin key hKeyLower hKeyUpper
  · rintro ⟨hLower, hUpper, hMin⟩
    refine ⟨hLower, hUpper, ?_⟩
    intro key hKeyLower hKeyUpper
    rw [hEqual candidate hLower hUpper, hEqual key hKeyLower hKeyUpper]
    exact hMin key hKeyLower hKeyUpper

theorem isIntervalMin_succ_iff {rank : ℕ → ℕ}
    {lower upper candidate : ℕ} :
    IsIntervalMin (fun key => (rank key).succ) lower upper candidate ↔
      IsIntervalMin rank lower upper candidate := by
  constructor
  · rintro ⟨hLower, hUpper, hMin⟩
    refine ⟨hLower, hUpper, ?_⟩
    intro key hKeyLower hKeyUpper
    exact Nat.le_of_succ_le_succ (hMin key hKeyLower hKeyUpper)
  · rintro ⟨hLower, hUpper, hMin⟩
    refine ⟨hLower, hUpper, ?_⟩
    intro key hKeyLower hKeyUpper
    exact Nat.succ_le_succ (hMin key hKeyLower hKeyUpper)

/--
Every nonempty closed inorder interval in a BST has a unique key of minimum
depth.

This is `lemma:unique-depth-minimum` in a form independent of the later
value/null-node encoding.
-/
theorem BST.existsUnique_intervalDepthMin {treeLower treeUpper : ℕ}
    (tree : BST treeLower treeUpper)
    {intervalLower intervalUpper : ℕ}
    (hInsideLower : treeLower ≤ intervalLower)
    (hNonempty : intervalLower ≤ intervalUpper)
    (hInsideUpper : intervalUpper < treeUpper) :
    ∃! key,
      IsIntervalMin (BST.depth tree) intervalLower intervalUpper key := by
  induction tree generalizing intervalLower intervalUpper with
  | empty boundary =>
      omega
  | @node treeLower root treeUpper left right ihLeft ihRight =>
      by_cases hRight : root < intervalLower
      · have hDepthEqual :
            ∀ key, intervalLower ≤ key → key ≤ intervalUpper →
              BST.depth (.node left right) key = (BST.depth right key).succ := by
          intro key hKeyLower _
          exact BST.depth_node_of_root_lt left right (by omega)
        have hMinIff :
            ∀ key,
              IsIntervalMin (BST.depth (.node left right))
                  intervalLower intervalUpper key ↔
                IsIntervalMin (BST.depth right)
                  intervalLower intervalUpper key := by
          intro key
          exact (isIntervalMin_congrOn hDepthEqual).trans
            isIntervalMin_succ_iff
        obtain ⟨key, hKeyMin, hKeyUnique⟩ :=
          ihRight (by omega) hNonempty hInsideUpper
        refine ⟨key, (hMinIff key).2 hKeyMin, ?_⟩
        intro other hOther
        exact hKeyUnique other ((hMinIff other).1 hOther)
      · by_cases hLeft : intervalUpper < root
        · have hDepthEqual :
              ∀ key, intervalLower ≤ key → key ≤ intervalUpper →
                BST.depth (.node left right) key = (BST.depth left key).succ := by
            intro key _ hKeyUpper
            exact BST.depth_node_of_lt_root left right (by omega)
          have hMinIff :
              ∀ key,
                IsIntervalMin (BST.depth (.node left right))
                    intervalLower intervalUpper key ↔
                  IsIntervalMin (BST.depth left)
                    intervalLower intervalUpper key := by
            intro key
            exact (isIntervalMin_congrOn hDepthEqual).trans
              isIntervalMin_succ_iff
          obtain ⟨key, hKeyMin, hKeyUnique⟩ :=
            ihLeft hInsideLower hNonempty hLeft
          refine ⟨key, (hMinIff key).2 hKeyMin, ?_⟩
          intro other hOther
          exact hKeyUnique other ((hMinIff other).1 hOther)
        · have hRootLower : intervalLower ≤ root := by omega
          have hRootUpper : root ≤ intervalUpper := by omega
          refine ⟨root, ⟨hRootLower, hRootUpper, ?_⟩, ?_⟩
          · intro key _ _
            simp [BST.depth]
          · intro key hKeyMin
            by_contra hKeyNe
            have hDepthPositive :
                0 < BST.depth (.node left right) key := by
              simp only [BST.depth, if_neg hKeyNe]
              split <;> omega
            have hDepthAtMostRoot :=
              hKeyMin.2.2 root hRootLower hRootUpper
            simp only [BST.depth_root] at hDepthAtMostRoot
            omega

end Splay.Tree
