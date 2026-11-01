import TangoSquared.CyclicCounts
import Mathlib.Algebra.BigOperators.Intervals

/-! Telescoping on the actual midpoint depth reference and primary prefix cells. -/

namespace TangoSquared
open Primary

namespace DepthTree

theorem children_disjoint (left : DepthTree a c) (right : DepthTree (c + 1) b) :
    Disjoint left.nodes right.nodes := by
  apply Finset.disjoint_left.mpr
  intro s hl hr
  have h₁ := left.node_bounds hl
  have h₂ := right.node_bounds hr
  omega

theorem root_not_left (left : DepthTree a c) (hcb : c < b) :
    (⟨a, c, b⟩ : DepthSplit) ∉ left.nodes := by
  intro h
  have hb := left.node_bounds h
  change a ≤ a ∧ a ≤ c ∧ c < b ∧ b ≤ c at hb
  omega

theorem root_not_right (right : DepthTree (c + 1) b) (hac : a ≤ c) :
    (⟨a, c, b⟩ : DepthSplit) ∉ right.nodes := by
  intro h
  have hb := right.node_bounds h
  change c + 1 ≤ a ∧ a ≤ c ∧ c < b ∧ b ≤ b at hb
  omega

/-- The concrete depth intervals telescope to all their singleton leaves. -/
theorem potential_telescope (t : DepthTree a b) (v : Nat → Nat → ℤ) :
    (∑ s ∈ t.nodes, (v s.lo s.cut + v (s.cut + 1) s.hi - v s.lo s.hi)) + v a b =
      ∑ d ∈ Finset.Icc a b, v d d := by
  induction t with
  | leaf a => simp [nodes]
  | @node a b c hac hcb left right ihl ihr =>
    rw [nodes, Finset.sum_insert]
    · rw [Finset.sum_union (children_disjoint left right)]
      have hi : Finset.Icc a b = Finset.Icc a c ∪ Finset.Icc (c + 1) b := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_union]
        omega
      have hd : Disjoint (Finset.Icc a c) (Finset.Icc (c + 1) b) := by
        apply Finset.disjoint_left.mpr
        intro d h₁ h₂
        simp only [Finset.mem_Icc] at h₁ h₂
        omega
      rw [hi, Finset.sum_union hd]
      dsimp only
      omega
    · simp only [Finset.mem_union, not_or]
      exact ⟨root_not_left left hcb, root_not_right right hac⟩

end DepthTree

/-- Sum of actual cyclic fine-cell turn counts over every depth-`a` owner. -/
def fragmentPotential (H : Nat) (xs : List Key) (a b : Nat) : ℤ :=
  ∑ u ∈ level a,
    (CyclicRuns.wordTurns ((ownerWord u xs).map (List.take (min (b + 1) H))) : ℤ)

def splitPotentialDifference (H : Nat) (xs : List Key) (s : DepthSplit) : ℤ :=
  fragmentPotential H xs s.lo s.cut + fragmentPotential H xs (s.cut + 1) s.hi -
    fragmentPotential H xs s.lo s.hi

theorem fragment_potential_telescope (H : Nat) (xs : List Key) :
    (∑ s ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes,
      splitPotentialDifference H xs s) + fragmentPotential H xs 0 H =
      ∑ d ∈ Finset.Icc 0 H, fragmentPotential H xs d d :=
  DepthTree.potential_telescope _ (fragmentPotential H xs)

end TangoSquared
