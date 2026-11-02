import ChaCha.Paper20261030.Potential

/-!
# Telescoping on concrete recursive interval splits

A `SplitDecomposition P` recursively applies monotone key contractions to
actual instances. Its two kinds of children are exactly the contracted
instance and the filtered segment instances. The alternation sum is
bounded independently of the shapes and depths of these finite splits.
-/

namespace ChaCha.Paper20261030.Rectangles

open scoped BigOperators

inductive SplitDecomposition : Finset Point → Type
  | leaf (P : Finset Point) : SplitDecomposition P
  | split {P : Finset Point} (f : Int → Int) (hf : Monotone f)
      (I : Finset Int) (hI : ∀ p ∈ P, f p.1 ∈ I)
      (outer : SplitDecomposition (project f P))
      (inner : (i : I) → SplitDecomposition (fiber f i.val P)) : SplitDecomposition P

noncomputable def SplitDecomposition.alternations : {P : Finset Point} → SplitDecomposition P → Nat
  | _, .leaf _ => 0
  | P, .split f _ I _ outer inner =>
      depthAlternations P f + outer.alternations + ∑ i : I, (inner i).alternations

noncomputable def SplitDecomposition.leafPotential : {P : Finset Point} → SplitDecomposition P → Int
  | P, .leaf _ => potential P
  | _, .split _ _ I _ outer inner =>
      outer.leafPotential + ∑ i : I, (inner i).leafPotential

theorem SplitDecomposition.telescope {P : Finset Point} (d : SplitDecomposition P)
    (hP : Instance P) : (d.alternations : Int) + d.leafPotential ≤ potential P := by
  induction d with
  | leaf P => simp only [alternations,leafPotential,Nat.cast_zero,zero_add,le_refl]
  | @split P f hf I hI outer inner ihouter ihinner =>
    have ho := ihouter (instance_project hP f)
    have hi : ∀ i : I, ((inner i).alternations : Int) + (inner i).leafPotential ≤
        potential (fiber f i.val P) := fun i => ihinner i (instance_fiber hP f i.val)
    have his := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    have hrelease := potential_split_release hP f hf I hI
    have hsubtype : (∑ i : I, potential (fiber f i.val P)) =
        ∑ i ∈ I, potential (fiber f i P) := by
      exact Finset.sum_coe_sort I (fun i => potential (fiber f i P))
    rw [Finset.sum_add_distrib,hsubtype] at his
    simp only [alternations,leafPotential,Nat.cast_add,Nat.cast_sum]
    omega

theorem SplitDecomposition.leafPotential_nonnegative {P : Finset Point}
    (d : SplitDecomposition P) (hP : Instance P) : 0 ≤ d.leafPotential := by
  induction d with
  | leaf P => exact potential_nonnegative hP
  | @split P f hf I hI outer inner ihouter ihinner =>
    exact add_nonneg (ihouter (instance_project hP f))
      (Finset.sum_nonneg (fun i _ => ihinner i (instance_fiber hP f i.val)))

/-- The full recursive split count is at most five times the rectangle bound. -/
theorem SplitDecomposition.alternations_le_rectangleBound {P : Finset Point}
    (d : SplitDecomposition P) (hP : Instance P) : d.alternations ≤ 5 * rectangleBound P := by
  have ht := d.telescope hP
  have hn := d.leafPotential_nonnegative hP
  have hm := potential_le_rectangleBound P
  omega

end ChaCha.Paper20261030.Rectangles
