import TangoSquared.Paper20261030.ActiveDirection
import TangoSquared.Reference
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Ring.Int

/-!
# Numeric coordinates of the perfect primary reference

Keys are integers from `0` through `2^H - 1`. Their depth-`d` ancestor
is their dyadic block index `x / 2^(H-d)`. The lowest common ancestor
(LCA) depth is the greatest depth at which the two block indices agree.
The secondary depth tree reuses the already formalized `DepthTree`.
-/

namespace TangoSquared.Paper20261030.Dyadic

open Rectangles

def coarsen (b c : Nat) (x : Int) : Int := x / (2 : Int) ^ (b - c)

def ValidKey (H : Nat) (x : Int) : Prop := 0 ≤ x ∧ x < (2 : Int) ^ H

theorem coarsen_mono (b c : Nat) : Monotone (coarsen b c) := by
  intro x y hxy
  exact Int.ediv_le_ediv (pow_pos (by decide) _) hxy

theorem coarsen_self (b : Nat) (x : Int) : coarsen b b x = x := by
  simp [coarsen]

theorem coarsen_comp {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) (x : Int) :
    coarsen b a (coarsen c b x) = coarsen c a x := by
  unfold coarsen
  rw [Int.ediv_ediv_of_nonneg (le_of_lt (pow_pos (by decide) _)),← pow_add]
  congr 2
  omega

theorem coarsen_zero {H : Nat} {x : Int} (hx : ValidKey H x) : coarsen H 0 x = 0 := by
  simp only [coarsen,Nat.sub_zero]
  exact Int.ediv_eq_zero_of_lt hx.1 hx.2

theorem coarsen_eq_of_deeper {a b H : Nat} (hab : a ≤ b) (hbH : b ≤ H)
    {x y : Int} (he : coarsen H b x = coarsen H b y) : coarsen H a x = coarsen H a y := by
  rw [← coarsen_comp hab hbH x,← coarsen_comp hab hbH y,he]

def commonDepths (H : Nat) (x y : Int) : Finset Nat :=
  (Finset.range (H + 1)).filter (fun d => coarsen H d x = coarsen H d y)

def lcaDepth (H : Nat) (x y : Int) : Nat := (commonDepths H x y).sup id

theorem commonDepths_nonempty {H : Nat} {x y : Int}
    (hx : ValidKey H x) (hy : ValidKey H y) : (commonDepths H x y).Nonempty := by
  refine ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
  rw [coarsen_zero hx,coarsen_zero hy]

theorem lcaDepth_mem {H : Nat} {x y : Int}
    (hx : ValidKey H x) (hy : ValidKey H y) : lcaDepth H x y ∈ commonDepths H x y := by
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup (commonDepths H x y)
    (commonDepths_nonempty hx hy) id
  change (commonDepths H x y).sup id ∈ _
  rw [he]
  exact hd

theorem lcaDepth_le {H : Nat} {x y : Int}
    (hx : ValidKey H x) (hy : ValidKey H y) : lcaDepth H x y ≤ H := by
  have hmem := lcaDepth_mem hx hy
  have := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  omega

theorem ancestor_eq_iff_le_lca {H d : Nat} {x y : Int}
    (hx : ValidKey H x) (hy : ValidKey H y) (hd : d ≤ H) :
    coarsen H d x = coarsen H d y ↔ d ≤ lcaDepth H x y := by
  constructor
  · intro he
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),he⟩)
  · intro hdL
    exact coarsen_eq_of_deeper hdL (lcaDepth_le hx hy) (Finset.mem_filter.mp (lcaDepth_mem hx hy)).2

/-- The three actual LCA cases for a fragment interval `[a,b)` split at `c`.
The unchanged case is precisely equality of depth-`b` block labels. -/
theorem fragment_direction_cases {H c b : Nat} {x y : Int}
    (hx : ValidKey H x) (hy : ValidKey H y) (hcb : c ≤ b) (hbH : b ≤ H) :
    (coarsen H b x = coarsen H b y ↔ b ≤ lcaDepth H x y) ∧
    (coarsen H b x ≠ coarsen H b y ∧
      coarsen b c (coarsen H b x) = coarsen b c (coarsen H b y) ↔
      c ≤ lcaDepth H x y ∧ lcaDepth H x y < b) ∧
    (coarsen b c (coarsen H b x) ≠ coarsen b c (coarsen H b y) ↔
      lcaDepth H x y < c) := by
  rw [coarsen_comp hcb hbH,coarsen_comp hcb hbH]
  simp only [ne_eq,ancestor_eq_iff_le_lca hx hy hbH,ancestor_eq_iff_le_lca hx hy (hcb.trans hbH)]
  constructor
  · trivial
  constructor <;> omega

end TangoSquared.Paper20261030.Dyadic
