import ChaCha.Paper20261030.FragmentTransport

/-!
# The manuscript's LCA alternation bound

The recursion always receives original access keys and original timestamps.
Its up child retains the subword and its down children filter that subword
by the actual primary descendant. At each node `lcaTransitions` counts the
DOWN-to-UP updates by the original keys' lowest common ancestor.
-/

namespace ChaCha.Paper20261030.Dyadic

open Rectangles
open scoped BigOperators

noncomputable def lcaBound (H : Nat) : {a b : Nat} → DepthTree a b → Finset Point → Nat
  | _, _, .leaf _, _ => 0
  | _, b, .node c _ _ left right, P =>
      lcaTransitions H (c + 1) (b + 1) P + lcaBound H left P +
        ∑ i ∈ P.image (fun p => coarsen H (c + 1) p.1),
          lcaBound H right (fiber (coarsen H (c + 1)) i P)

theorem lcaBound_eq_fragmentAlternations {H a b : Nat} (t : DepthTree a b)
    {P : Finset Point} (hP : Instance P) (hkeys : ∀ p ∈ P, ValidKey H p.1)
    (hbH : b + 1 ≤ H) :
    lcaBound H t P = fragmentAlternations t (project (coarsen H (b + 1)) P) := by
  induction t generalizing P with
  | leaf a => rfl
  | @node a b c ha hb left right ihl ihr =>
    have hcb : c + 1 ≤ b + 1 := by omega
    have hcH : c + 1 ≤ H := hcb.trans hbH
    simp only [lcaBound,fragmentAlternations]
    rw [lcaTransitions_eq_depthAlternations hP hkeys hcb hbH,
      depthAlternations_eq_downUp (instance_project hP (coarsen H (b + 1))),
      ihl hP hkeys hcH,project_coarsen_comp hcb hbH,
      visited_indices_coarsen hcb hbH]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [fiber_project_coarsen hcb hbH]
    exact ihr (instance_fiber hP _ i)
      (fun p hp => hkeys p (Finset.mem_filter.mp hp).1) hbH

/-- LCA alternations of every fragment are bounded by five times the actual
rectangle maximum, for every access sequence on the perfect primary tree
and every full ordered secondary reference on its internal depths. -/
theorem lcaBound_le_rectangleBound {h : Nat} (t : DepthTree 0 h)
    {P : Finset Point} (hP : Instance P) (hkeys : ∀ p ∈ P, ValidKey (h + 1) p.1) :
    lcaBound (h + 1) t P ≤ 5 * rectangleBound P := by
  rw [lcaBound_eq_fragmentAlternations t hP hkeys (Nat.le_refl _),project_self]
  exact fragmentAlternations_le_rectangleBound t hP

/-- The balanced depth reference used by Cha-Cha. -/
theorem midpoint_lcaBound_le_rectangleBound {h : Nat}
    {P : Finset Point} (hP : Instance P) (hkeys : ∀ p ∈ P, ValidKey (h + 1) p.1) :
    lcaBound (h + 1) (DepthTree.midpoint 0 h (Nat.zero_le h)) P ≤ 5 * rectangleBound P :=
  lcaBound_le_rectangleBound _ hP hkeys

end ChaCha.Paper20261030.Dyadic
