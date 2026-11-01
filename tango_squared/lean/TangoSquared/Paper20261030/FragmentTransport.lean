import TangoSquared.Paper20261030.LCAState

/-!
# Exact transport of fragment instances

Projection to a shallower primary level composes, and filtering by a
shallower block commutes with projecting to a deeper block. These identities
identify the recursion's children with the manuscript's original subwords.
-/

namespace TangoSquared.Paper20261030.Dyadic

open Rectangles

theorem project_comp (f g : Int → Int) (P : Finset Point) :
    project f (project g P) = project (fun x => f (g x)) P := by
  unfold project
  rw [Finset.image_image]
  rfl

theorem project_coarsen_comp {a b H : Nat} (hab : a ≤ b) (hbH : b ≤ H) (P : Finset Point) :
    project (coarsen b a) (project (coarsen H b) P) = project (coarsen H a) P := by
  rw [project_comp]
  congr 1
  funext x
  exact coarsen_comp hab hbH x

theorem fiber_project (f g : Int → Int) (i : Int) (P : Finset Point) :
    fiber f i (project g P) = project g (fiber (fun x => f (g x)) i P) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp,hcolor⟩ := Finset.mem_filter.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hcolor⟩,rfl⟩
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqP,hcolor⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,hqP,rfl⟩,hcolor⟩

theorem fiber_project_coarsen {a b H : Nat} (hab : a ≤ b) (hbH : b ≤ H)
    (i : Int) (P : Finset Point) :
    fiber (coarsen b a) i (project (coarsen H b) P) =
      project (coarsen H b) (fiber (coarsen H a) i P) := by
  rw [fiber_project]
  have he : (fun x => coarsen b a (coarsen H b x)) = coarsen H a :=
    funext (coarsen_comp hab hbH)
  rw [he]

theorem visited_indices_coarsen {a b H : Nat} (hab : a ≤ b) (hbH : b ≤ H)
    (P : Finset Point) :
    (project (coarsen H b) P).image (fun p => coarsen b a p.1) =
      P.image (fun p => coarsen H a p.1) := by
  unfold project
  rw [Finset.image_image]
  apply Finset.image_congr
  intro p hp
  exact coarsen_comp hab hbH p.1

theorem project_self (H : Nat) (P : Finset Point) : project (coarsen H H) P = P := by
  have he : mapPoint (coarsen H H) = id := by
    funext p
    exact Prod.ext (coarsen_self H p.1) rfl
  simp only [project,he,Finset.image_id]

end TangoSquared.Paper20261030.Dyadic
