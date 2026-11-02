import ChaCha.Paper20261030.LCABound
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Summing over nested primary fibers

A fine primary block belongs to exactly one coarse block. These identities
collapse nested sums over visited blocks, including empty instances.
-/

namespace ChaCha.Paper20261030.Rectangles

open scoped BigOperators

theorem fiber_image_refinement (P : Finset Point) (f g k : Int → Int)
    (hcomp : ∀ x, f x = k (g x)) (i : Int) :
    (fiber f i P).image (fun p => g p.1) =
      (P.image (fun p => g p.1)).filter (fun j => k j = i) := by
  ext j
  constructor
  · intro hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,by rw [← hcomp,hi]⟩
  · intro hj
    obtain ⟨hj,hi⟩ := Finset.mem_filter.mp hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,by rw [hcomp,hi]⟩,rfl⟩

theorem fiber_fiber_refinement (P : Finset Point) (f g k : Int → Int)
    (hcomp : ∀ x, f x = k (g x)) {i j : Int} (hi : k j = i) :
    fiber g j (fiber f i P) = fiber g j P := by
  ext p
  simp only [fiber,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hp,hj⟩
    exact ⟨⟨hp,by rw [hcomp,hj,hi]⟩,hj⟩

theorem sum_visited_refinement (P : Finset Point) (f g k : Int → Int)
    (hcomp : ∀ x, f x = k (g x)) (F : Int → Nat) :
    (∑ i ∈ P.image (fun p => f p.1), ∑ j ∈ (fiber f i P).image (fun p => g p.1), F j) =
      ∑ j ∈ P.image (fun p => g p.1), F j := by
  simp only [fiber_image_refinement P f g k hcomp,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
  have hi : k (g p.1) ∈ P.image (fun p => f p.1) :=
    Finset.mem_image.mpr ⟨p,hp,hcomp p.1⟩
  simp [hi]

theorem sum_fibers_refinement (P : Finset Point) (f g k : Int → Int)
    (hcomp : ∀ x, f x = k (g x)) (F : Int → Finset Point → Nat) :
    (∑ i ∈ P.image (fun p => f p.1),
      ∑ j ∈ (fiber f i P).image (fun p => g p.1), F j (fiber g j (fiber f i P))) =
      ∑ j ∈ P.image (fun p => g p.1), F j (fiber g j P) := by
  calc
    _ = ∑ i ∈ P.image (fun p => f p.1),
        ∑ j ∈ (fiber f i P).image (fun p => g p.1), F j (fiber g j P) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hji : k j = i := by
        rw [fiber_image_refinement P f g k hcomp] at hj
        exact (Finset.mem_filter.mp hj).2
      rw [fiber_fiber_refinement P f g k hcomp hji]
    _ = _ := sum_visited_refinement P f g k hcomp _

end ChaCha.Paper20261030.Rectangles

namespace ChaCha.Paper20261030.Dyadic

open Rectangles
open scoped BigOperators

noncomputable def ownedLCA (H : Nat) {a b : Nat} (t : DepthTree a b) (P : Finset Point) : Nat :=
  ∑ i ∈ P.image (fun p => coarsen H a p.1), lcaBound H t (fiber (coarsen H a) i P)

noncomputable def flatLCA (H : Nat) : {a b : Nat} → DepthTree a b → Finset Point → Nat
  | _, _, .leaf _, _ => 0
  | a, b, .node c _ _ l r, P =>
      (∑ i ∈ P.image (fun p => coarsen H a p.1),
        lcaTransitions H (c + 1) (b + 1) (fiber (coarsen H a) i P)) +
        flatLCA H l P + flatLCA H r P

theorem ownedLCA_eq_flatLCA {H a b : Nat} (t : DepthTree a b) (hb : b < H)
    (P : Finset Point) : ownedLCA H t P = flatLCA H t P := by
  induction t with
  | leaf a => simp [ownedLCA,lcaBound,flatLCA]
  | @node a b c ha hcb l r ihl ihr =>
    have hc : c < H := by omega
    unfold ownedLCA
    simp only [lcaBound,Finset.sum_add_distrib]
    change _ = _ + _ + _
    rw [sum_fibers_refinement P (coarsen H a) (coarsen H (c + 1)) (coarsen (c + 1) a)
      (fun x => (coarsen_comp (by omega : a ≤ c + 1) (by omega : c + 1 ≤ H) x).symm)]
    change _ + ownedLCA H l P + ownedLCA H r P = _
    rw [ihl hc,ihr hb]

theorem lcaBound_empty {H a b : Nat} (t : DepthTree a b) : lcaBound H t ∅ = 0 := by
  induction t with
  | leaf a => rfl
  | node c ha hb l r ihl ihr => simp [lcaBound,lcaTransitions,eventCount,ihl]

theorem root_flatLCA {H b : Nat} (t : DepthTree 0 b) (hb : b < H)
    (P : Finset Point) (hkeys : ∀ p ∈ P, ValidKey H p.1) : flatLCA H t P = lcaBound H t P := by
  rw [← ownedLCA_eq_flatLCA t hb]
  by_cases he : P = ∅
  · subst P; simp [ownedLCA,lcaBound_empty]
  · have hne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    have hi : P.image (fun p => coarsen H 0 p.1) = {0} := by
      ext i
      constructor
      · intro hi
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
        simp [coarsen_zero (hkeys p hp)]
      · intro hi
        have hi0 := Finset.mem_singleton.mp hi
        subst i
        obtain ⟨p,hp⟩ := hne
        exact Finset.mem_image.mpr ⟨p,hp,coarsen_zero (hkeys p hp)⟩
    have hf : fiber (coarsen H 0) 0 P = P := by
      ext p
      simp only [fiber,Finset.mem_filter]
      exact ⟨And.left,fun hp => ⟨hp,coarsen_zero (hkeys p hp)⟩⟩
    simp only [ownedLCA,hi,Finset.sum_singleton,hf]

end ChaCha.Paper20261030.Dyadic
