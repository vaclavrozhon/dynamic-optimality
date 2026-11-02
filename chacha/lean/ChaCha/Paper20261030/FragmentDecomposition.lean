import ChaCha.Paper20261030.DyadicReference

/-!
# The concrete fragment hierarchy of a perfect primary tree

`DepthTree a b` uses inclusive depth endpoints; it represents the paper's
half-open interval `[a,b+1)`. Splitting at its stored cut `c` contracts
primary labels to depth `c+1` for the up child and filters by each visited
depth-`c+1` descendant for the down children. Unvisited descendants contain
no input events and contribute zero.
-/

namespace ChaCha.Paper20261030.Dyadic

open Rectangles
open scoped BigOperators

noncomputable def fragmentDecomposition : {a b : Nat} → DepthTree a b →
    (P : Finset Point) → SplitDecomposition P
  | _, _, .leaf _, P => .leaf P
  | _, b, .node c _ _ left right, P =>
      let f := coarsen (b + 1) (c + 1)
      let I := P.image (fun p => f p.1)
      .split f (coarsen_mono _ _) I
        (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
        (fragmentDecomposition left (project f P))
        (fun i => fragmentDecomposition right (fiber f i.val P))

/-- Actual DOWN-to-UP changes of all visited fragments in the depth tree. -/
noncomputable def fragmentAlternations : {a b : Nat} → DepthTree a b → Finset Point → Nat
  | _, _, .leaf _, _ => 0
  | _, b, .node c _ _ left right, P =>
      let f := coarsen (b + 1) (c + 1)
      let I := P.image (fun p => f p.1)
      eventCount P (DownUpAt P f) + fragmentAlternations left (project f P) +
        ∑ i ∈ I, fragmentAlternations right (fiber f i P)

theorem fragmentAlternations_eq_decomposition {a b : Nat} (t : DepthTree a b)
    {P : Finset Point} (hP : Instance P) :
    fragmentAlternations t P = (fragmentDecomposition t P).alternations := by
  induction t generalizing P with
  | leaf a => rfl
  | @node a b c ha hb left right ihl ihr =>
    simp only [fragmentAlternations,fragmentDecomposition,SplitDecomposition.alternations]
    rw [← depthAlternations_eq_downUp hP,
      ihl (instance_project hP (coarsen (b + 1) (c + 1)))]
    congr 1
    rw [Finset.sum_coe_sort (P.image (fun p => coarsen (b + 1) (c + 1) p.1))
      (fun i => (fragmentDecomposition right (fiber (coarsen (b + 1) (c + 1)) i P)).alternations)]
    apply Finset.sum_congr rfl
    intro i hi
    exact ihr (instance_fiber hP _ i)

/-- Concrete dyadic fragment bound, with the manuscript's constant five. -/
theorem fragmentAlternations_le_rectangleBound {a b : Nat} (t : DepthTree a b)
    {P : Finset Point} (hP : Instance P) : fragmentAlternations t P ≤ 5 * rectangleBound P := by
  rw [fragmentAlternations_eq_decomposition t hP]
  exact (fragmentDecomposition t P).alternations_le_rectangleBound hP

/-- All keys of a fragment have one depth-`a` primary owner. -/
def HasOwner (a b : Nat) (u : Int) (P : Finset Point) : Prop :=
  ∀ p ∈ P, coarsen b a p.1 = u

theorem outer_hasOwner {a c b : Nat} (hac : a ≤ c) (hcb : c ≤ b)
    {u : Int} {P : Finset Point} (howner : HasOwner a b u P) :
    HasOwner a c u (project (coarsen b c) P) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  change coarsen c a (coarsen b c q.1) = u
  rw [coarsen_comp hac hcb]
  exact howner q hq

theorem inner_hasOwner (c b : Nat) (i : Int) (P : Finset Point) :
    HasOwner c b i (fiber (coarsen b c) i P) := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem visited_child_descends {a c b : Nat} (hac : a ≤ c) (hcb : c ≤ b)
    {u i : Int} {P : Finset Point} (howner : HasOwner a b u P)
    (hi : i ∈ P.image (fun p => coarsen b c p.1)) : coarsen c a i = u := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
  rw [coarsen_comp hac hcb]
  exact howner p hp

theorem fragmentAlternations_empty {a b : Nat} (t : DepthTree a b) :
    fragmentAlternations t ∅ = 0 := by
  induction t with
  | leaf a => rfl
  | @node a b c ha hb left right ihl ihr =>
    simp [fragmentAlternations,project,eventCount,ihl]

/-- The initial fragment is the whole primary tree. -/
theorem root_hasOwner {H : Nat} {P : Finset Point}
    (hkeys : ∀ p ∈ P, ValidKey H p.1) : HasOwner 0 H 0 P := by
  intro p hp
  exact coarsen_zero (hkeys p hp)

end ChaCha.Paper20261030.Dyadic
