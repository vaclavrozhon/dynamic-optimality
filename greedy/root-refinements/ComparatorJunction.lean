import RotationIntervalMin
import SingleJunction

/-!
Composition of the concrete comparator interval-minimum theorem and the
ordered-tree fork theorem. A rotation anywhere in a concrete comparator BST
changes at most one outgoing heavy branch in any fixed ordinary refinement.
The selected owners are actual unique minima of comparator external depths.
No owner-swap or junction-count premise remains in the final theorem.

This does not yet verify the associated ordered heap/block splice.
-/

namespace GreedyMerge

open Splay.Tree
open Splay.Tree.BST
open Junction

noncomputable def intervalOwner {n : ℕ} (comparator : BST 0 n) (lo hi : ℕ) : ℕ :=
  if h : lo ≤ hi ∧ hi ≤ n then
    Classical.choose (comparator.existsUnique_intervalExternalDepthMin
      (intervalLower := 2 * lo) (intervalUpper := 2 * hi)
      (by omega) (by omega) (by omega))
  else 0

theorem intervalOwner_isMin {n lo hi : ℕ} (comparator : BST 0 n)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    IsIntervalMin comparator.externalDepth (2 * lo) (2 * hi)
      (intervalOwner comparator lo hi) := by
  unfold intervalOwner
  rw [dif_pos ⟨hlo, hhi⟩]
  exact (Classical.choose_spec (comparator.existsUnique_intervalExternalDepthMin
    (intervalLower := 2 * lo) (intervalUpper := 2 * hi)
    (by omega) (by omega) (by omega))).1

theorem intervalOwner_unique {n lo hi candidate : ℕ} (comparator : BST 0 n)
    (hlo : lo ≤ hi) (hhi : hi ≤ n)
    (hmin : IsIntervalMin comparator.externalDepth (2 * lo) (2 * hi) candidate) :
    candidate = intervalOwner comparator lo hi := by
  obtain ⟨owner, howner, hunique⟩ :=
    comparator.existsUnique_intervalExternalDepthMin
      (intervalLower := 2 * lo) (intervalUpper := 2 * hi)
      (by omega) (by omega) (by omega)
  have hc := hunique candidate hmin
  have ho := hunique (intervalOwner comparator lo hi)
    (intervalOwner_isMin comparator hlo hhi)
  exact hc.trans ho.symm

theorem intervalOwner_inside {n lo hi : ℕ} (comparator : BST 0 n)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    Within lo hi (intervalOwner comparator lo hi) := by
  have h := intervalOwner_isMin comparator hlo hhi
  exact ⟨h.1, h.2.1⟩

theorem KeyRotationAt.intervalOwner_changes
    {n demoted promoted depth : ℕ} {before after : BST 0 n}
    (step : KeyRotationAt demoted promoted depth before after)
    {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    intervalOwner before lo hi = intervalOwner after lo hi ∨
      (intervalOwner before lo hi = 2 * demoted + 1 ∧
        intervalOwner after lo hi = 2 * promoted + 1) := by
  rcases step.intervalMin (intervalOwner_isMin before hlo hhi) with hstay | ⟨ha, hb⟩
  · exact Or.inl (intervalOwner_unique after hlo hhi hstay)
  · exact Or.inr ⟨ha, (intervalOwner_unique after hlo hhi hb).symm⟩

/-- Any comparator rotation, at arbitrary depth, changes at most one actual
outgoing heavy branch of an arbitrary fixed refinement on the same keys. -/
theorem comparisonRotation_junctionCount_le_one
    {n depth : ℕ} {before after : BST 0 n}
    (refinement : BST 0 n) (step : RotationAt depth before after) :
    JunctionCount (intervalOwner before) (intervalOwner after) refinement ≤ 1 := by
  obtain ⟨a, b, keyStep⟩ := exists_keyRotationAt step
  apply junctionCount_le_one (a := 2 * a + 1) (b := 2 * b + 1)
    refinement (intervalOwner before) (intervalOwner after) (Nat.le_refl n)
  · intro lo hi hlo hhi
    exact intervalOwner_inside before hlo hhi
  · intro lo hi hlo hhi
    exact intervalOwner_inside after hlo hhi
  · intro lo hi hlo hhi
    exact keyStep.intervalOwner_changes hlo hhi

end GreedyMerge

#print axioms GreedyMerge.comparisonRotation_junctionCount_le_one
