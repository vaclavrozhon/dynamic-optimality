import TangoSquared.Paper20261030.SecondaryFlipBound
import TangoSquared.Paper20261030.DyadicReference

/-!
# The canonical numeric primary reference

`canonical h owner` is the perfect primary subtree consisting of all
integers whose quotient by `2^h` is `owner`. The whole reference is
`canonical H 0`. Its initial preferences point right, as in the manuscript.
This construction connects concrete tree operations with dyadic ancestors.
-/

namespace TangoSquared.Paper20261030.Dyadic

open PreferredProjection

def canonical : Nat → Int → PrefRouter Int
  | 0, owner => .leaf owner
  | h + 1, owner => .fork true (canonical h (2 * owner)) (canonical h (2 * owner + 1))

theorem canonical_perfect (h : Nat) (owner : Int) : (canonical h owner).Perfect h := by
  induction h generalizing owner with
  | zero => trivial
  | succ h ih => exact ⟨ih _,ih _⟩

theorem div_pow_succ (x : Int) (h : Nat) :
    x / (2 : Int) ^ (h + 1) = (x / (2 : Int) ^ h) / 2 := by
  rw [Int.ediv_ediv_of_nonneg (show (0 : Int) ≤ 2 ^ h from (pow_pos (by decide) _).le),pow_succ]

theorem canonical_mem (h : Nat) (owner x : Int) :
    x ∈ (canonical h owner).leaves ↔ x / (2 : Int) ^ h = owner := by
  induction h generalizing owner with
  | zero => simp [canonical,PrefRouter.leaves]
  | succ h ih =>
    simp only [canonical,PrefRouter.leaves,List.mem_append,ih,div_pow_succ]
    omega

theorem canonical_nodup (h : Nat) (owner : Int) : (canonical h owner).leaves.Nodup := by
  induction h generalizing owner with
  | zero => simp [canonical,PrefRouter.leaves]
  | succ h ih =>
    apply List.nodup_append.mpr
    refine ⟨ih _,ih _,?_⟩
    intro x hx y hy he
    have hx' := (canonical_mem h (2 * owner) x).mp hx
    have hy' := (canonical_mem h (2 * owner + 1) y).mp hy
    subst y
    omega

theorem canonical_zero_mem (H : Nat) (x : Int) :
    x ∈ (canonical H 0).leaves ↔ ValidKey H x := by
  rw [canonical_mem]
  have hpos : (0 : Int) < 2 ^ H := pow_pos (by decide) _
  constructor
  · intro h
    have hrem : x % (2 : Int) ^ H = x := by
      have := Int.emod_add_ediv_mul x ((2 : Int) ^ H)
      simp only [h,zero_mul,add_zero] at this
      exact this
    constructor
    · rw [← hrem]; exact Int.emod_nonneg _ (ne_of_gt hpos)
    · rw [← hrem]; exact Int.emod_lt_of_pos _ hpos
  · intro h
    exact Int.ediv_eq_zero_of_lt h.1 h.2

/-- A deeper quotient determines every ancestor quotient. -/
theorem quotient_coarse {h d : Nat} (hd : d ≤ h) {x y : Int}
    (he : x / (2 : Int) ^ (h - d) = y / (2 : Int) ^ (h - d)) :
    x / (2 : Int) ^ h = y / (2 : Int) ^ h := by
  have he' := congrArg (fun z : Int => z / (2 : Int) ^ d) he
  rw [Int.ediv_ediv_of_nonneg (show (0 : Int) ≤ 2 ^ (h - d) from (pow_pos (by decide) _).le),
    Int.ediv_ediv_of_nonneg (show (0 : Int) ≤ 2 ^ (h - d) from (pow_pos (by decide) _).le),
    ← pow_add] at he'
  simpa only [Nat.sub_add_cancel hd] using he'

/-- Ancestor equality in the actual primary tree is exactly dyadic block
equality, including the leaf depth for repeated keys. -/
theorem canonical_ancestor_iff (h : Nat) (owner x y : Int)
    (hx : x ∈ (canonical h owner).leaves) (hy : y ∈ (canonical h owner).leaves)
    (d : Nat) (hd : d ≤ h) :
    x / (2 : Int) ^ (h - d) = y / (2 : Int) ^ (h - d) ↔
      d ≤ (canonical h owner).referenceLCA x y := by
  induction h generalizing owner d with
  | zero =>
    have hd0 : d = 0 := by omega
    subst d
    have hx' := (canonical_mem 0 owner x).mp hx
    have hy' := (canonical_mem 0 owner y).mp hy
    simp only [pow_zero,Int.ediv_one] at hx' hy'
    simp [canonical,PrefRouter.referenceLCA,hx',hy']
  | succ h ih =>
    cases d with
    | zero =>
      have hx' := (canonical_mem (h + 1) owner x).mp hx
      have hy' := (canonical_mem (h + 1) owner y).mp hy
      simp [hx',hy']
    | succ d =>
      have hd' : d ≤ h := by omega
      have hxp := (canonical_mem (h + 1) owner x).mp hx
      have hyp := (canonical_mem (h + 1) owner y).mp hy
      rw [div_pow_succ] at hxp hyp
      have hxalt : x / (2 : Int) ^ h = 2 * owner ∨ x / (2 : Int) ^ h = 2 * owner + 1 := by omega
      have hyalt : y / (2 : Int) ^ h = 2 * owner ∨ y / (2 : Int) ^ h = 2 * owner + 1 := by omega
      have hcoarse := quotient_coarse (x := x) (y := y) hd'
      simp only [Nat.add_sub_add_right,canonical,PrefRouter.referenceLCA,canonical_mem]
      rcases hxalt with hxl | hxr <;> rcases hyalt with hyl | hyr
      · have hi := ih (2 * owner) ((canonical_mem h _ x).mpr hxl)
          ((canonical_mem h _ y).mpr hyl) d hd'
        simp only [hxl,hyl,true_and,false_and,↓reduceIte]
        omega
      · have hne : x / (2 : Int) ^ (h - d) ≠ y / (2 : Int) ^ (h - d) := by
          intro he; have := hcoarse he; omega
        simp only [hxl,hyr,show 2 * owner ≠ 2 * owner + 1 by omega,
          show 2 * owner + 1 ≠ 2 * owner by omega,true_and,false_and,↓reduceIte]
        omega
      · have hne : x / (2 : Int) ^ (h - d) ≠ y / (2 : Int) ^ (h - d) := by
          intro he; have := hcoarse he; omega
        simp only [hxr,hyl,show 2 * owner ≠ 2 * owner + 1 by omega,
          show 2 * owner + 1 ≠ 2 * owner by omega,true_and,false_and,↓reduceIte]
        omega
      · have hi := ih (2 * owner + 1) ((canonical_mem h _ x).mpr hxr)
          ((canonical_mem h _ y).mpr hyr) d hd'
        simp only [hxr,hyr,show 2 * owner + 1 ≠ 2 * owner by omega,true_and,false_and,↓reduceIte]
        omega

theorem referenceLCA_le_height (t : PrefRouter Int) (x y : Int) :
    t.referenceLCA x y ≤ t.height := by
  induction t with
  | leaf a => rfl
  | fork b l r ihl ihr =>
    simp only [PrefRouter.referenceLCA,PrefRouter.height]
    split_ifs <;> omega

/-- The local depth of an LCA, plus the actual owner's depth, is exactly
the numeric LCA depth used by the rectangle lower bound. -/
theorem canonical_lca_offset {H h : Nat} (hh : h ≤ H) (owner x y : Int)
    (hx : ValidKey H x) (hy : ValidKey H y)
    (hxm : x ∈ (canonical h owner).leaves) (hym : y ∈ (canonical h owner).leaves) :
    H - h + (canonical h owner).referenceLCA x y = lcaDepth H x y := by
  have htree := referenceLCA_le_height (canonical h owner) x y
  rw [PrefRouter.perfect_height (canonical_perfect h owner)] at htree
  have hnum := lcaDepth_le hx hy
  have hstart : H - h ≤ lcaDepth H x y := by
    apply (ancestor_eq_iff_le_lca hx hy (by omega : H - h ≤ H)).mp
    have he : H - (H - h) = h := by omega
    simp only [coarsen,he]
    rw [(canonical_mem h owner x).mp hxm,(canonical_mem h owner y).mp hym]
  have hforward : H - h + (canonical h owner).referenceLCA x y ≤ lcaDepth H x y := by
    apply (ancestor_eq_iff_le_lca hx hy (by omega)).mp
    have he := (canonical_ancestor_iff h owner x y hxm hym _ htree).mpr (Nat.le_refl _)
    have hexp : H - (H - h + (canonical h owner).referenceLCA x y) =
        h - (canonical h owner).referenceLCA x y := by omega
    simpa only [coarsen,hexp] using he
  have hback : lcaDepth H x y - (H - h) ≤ (canonical h owner).referenceLCA x y := by
    apply (canonical_ancestor_iff h owner x y hxm hym _ (by omega)).mp
    have he := (Finset.mem_filter.mp (lcaDepth_mem hx hy)).2
    have hexp : h - (lcaDepth H x y - (H - h)) = H - lcaDepth H x y := by omega
    simpa only [coarsen,hexp] using he
  omega

theorem canonical_lca {H : Nat} {x y : Int} (hx : ValidKey H x) (hy : ValidKey H y) :
    (canonical H 0).referenceLCA x y = lcaDepth H x y := by
  simpa using canonical_lca_offset (Nat.le_refl H) 0 x y hx hy
    ((canonical_zero_mem H x).mpr hx) ((canonical_zero_mem H y).mpr hy)

def descendantIndex : Int → List Bool → Int
  | owner, [] => owner
  | owner, b :: bs => descendantIndex (2 * owner + if b then 1 else 0) bs

theorem canonical_atPath (h : Nat) (owner : Int) (u : List Bool) (hu : u.length ≤ h) :
    (canonical h owner).atPath u = some (canonical (h - u.length) (descendantIndex owner u)) := by
  induction u generalizing h owner with
  | nil => rfl
  | cons b u ih =>
    cases h with
    | zero => simp at hu
    | succ h =>
      have hu' : u.length ≤ h := by simp only [List.length_cons] at hu; omega
      cases b <;> simpa [canonical,PrefRouter.atPath,descendantIndex] using ih _ _ hu'

end TangoSquared.Paper20261030.Dyadic
