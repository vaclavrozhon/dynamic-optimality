import Splay.Tree.Rotation
import PortRotationCases

/-!
Concrete rotation lifting through full gap substitution. This is the final
ordered-fringe interface: separator rotations lift one-for-one, and a single
changed gap lifts through the unchanged separator skeleton at no extra cost.
-/
namespace GreedyMerge.ExpansionRotations
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.PortCases

/-- The first gap begins at the current hierarchy interval's lower bound. -/
def GapLower (start : ℕ) (separator : ℕ → ℕ) : ℕ → ℕ
  | 0 => start
  | i + 1 => separator i + 1

def Expand (start : ℕ) (separator : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower start separator i) (separator i))
    {lo hi : ℕ} : BST lo hi → BST (GapLower start separator lo) (separator hi)
  | .empty i => gaps i
  | .node left right => .node (Expand start separator gaps left) (Expand start separator gaps right)

theorem expand_rotation {lo hi depth : ℕ} {before after : BST lo hi}
    (start : ℕ) (separator : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower start separator i) (separator i))
    (step : RotationAt depth before after) :
    RotationAt depth (Expand start separator gaps before) (Expand start separator gaps after) := by
  induction step with
  | root rootStep =>
      cases rootStep with
      | right a b c => exact .root (.right _ _ _)
      | left a b c => exact .root (.left _ _ _)
  | leftContext step right ih => exact .leftContext ih _
  | rightContext left step ih => exact .rightContext _ ih

theorem expand_steps {lo hi count : ℕ} {before after : BST lo hi}
    (start : ℕ) (separator : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower start separator i) (separator i))
    (steps : RotationSteps count before after) :
    RotationSteps count (Expand start separator gaps before) (Expand start separator gaps after) := by
  induction steps with
  | refl => exact .refl _
  | cons step rest ih => exact .cons (expand_rotation start separator gaps step) ih

theorem expand_eq_of_gaps_eq {lo hi : ℕ}
    (start : ℕ) (separator : ℕ → ℕ)
    (gaps gaps' : ∀ i, BST (GapLower start separator i) (separator i))
    (tree : BST lo hi)
    (heq : ∀ i, lo ≤ i → i ≤ hi → gaps i = gaps' i) :
    Expand start separator gaps tree = Expand start separator gaps' tree := by
  induction tree with
  | empty i => exact heq i (by omega) (by omega)
  | @node lo root hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft (fun i hil hir => heq i hil (by omega))
      have hright := ihRight (fun i hil hir => heq i (by omega) hir)
      simp only [Expand, hleft, hright]

theorem expand_one_gap {lo hi key count : ℕ}
    (start : ℕ) (separator : ℕ → ℕ)
    (gaps gaps' : ∀ i, BST (GapLower start separator i) (separator i))
    (tree : BST lo hi) (hlo : lo ≤ key) (hhi : key ≤ hi)
    (heq : ∀ i, lo ≤ i → i ≤ hi → i ≠ key → gaps i = gaps' i)
    (steps : RotationSteps count (gaps key) (gaps' key)) :
    RotationSteps count (Expand start separator gaps tree) (Expand start separator gaps' tree) := by
  induction tree with
  | empty i =>
      have hkey : key = i := by omega
      subst key
      exact steps
  | @node lo root hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      by_cases hkey : key ≤ root
      · have hleft := ihLeft hlo hkey
          (fun i hil hir hne => heq i hil (by omega) hne)
        have hright := expand_eq_of_gaps_eq start separator gaps gaps' right
          (fun i hil hir => heq i (by omega) hir (by omega))
        simp only [Expand]
        rw [← hright]
        exact hleft.leftContext _
      · have hleft := expand_eq_of_gaps_eq start separator gaps gaps' left
          (fun i hil hir => heq i hil (by omega) (by omega))
        have hright := ihRight (by omega) hhi
          (fun i hil hir hne => heq i (by omega) hir hne)
        simp only [Expand]
        rw [← hleft]
        exact hright.rightContext _

end GreedyMerge.ExpansionRotations

#print axioms GreedyMerge.ExpansionRotations.expand_steps
#print axioms GreedyMerge.ExpansionRotations.expand_one_gap
