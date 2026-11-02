import ChaCha.Separation.FragmentCharges
import ChaCha.Separation.SparseKeys

/-!
# Fragment alternations of the sparse request family

At each active midpoint split, all smaller sparse keys remain in cell
zero and the largest surviving key is the only key in cell one. The
projected child sees only zero and one, and the nonzero fiber is constant.
Every local DOWN-to-UP event is therefore charged to an occurrence that
is removed before the recursive step.
-/

namespace ChaCha.Separation

open Paper20261030 Paper20261030.Rectangles Paper20261030.Dyadic
open scoped BigOperators

theorem fragmentAlternations_singleton_split {a b cut : Nat}
    (lower : a ≤ cut) (upper : cut < b) (left : DepthTree a cut)
    (right : DepthTree (cut+1) b) (points : Finset Point) (valid : Instance points)
    (exception : Int) (exceptionCell : coarsen (b+1) (cut+1) exception = 1)
    (cells : ∀ point ∈ points, coarsen (b+1) (cut+1) point.1 = 0 ∨ point.1 = exception)
    (recursive : fragmentAlternations right (fiber (coarsen (b+1) (cut+1)) 0 points) ≤
      (fiber (coarsen (b+1) (cut+1)) 0 points).card) :
    fragmentAlternations (.node cut lower upper left right) points ≤ points.card := by
  classical
  let projection := coarsen (b+1) (cut+1)
  have different : projection exception ≠ 0 := by change coarsen _ _ _ ≠ 0; omega
  have projected : fragmentAlternations left (project projection points) = 0 := by
    apply fragmentAlternations_small _ _ (instance_project valid projection)
    intro point member
    obtain ⟨original,present,rfl⟩ := Finset.mem_image.mp member
    change 0 ≤ projection original.1 ∧ projection original.1 ≤ 1
    rcases cells original present with zero | singleton
    · change projection original.1 = 0 at zero
      simp [zero]
    · rw [singleton]
      change 0 ≤ coarsen _ _ exception ∧ coarsen _ _ exception ≤ 1
      omega
  have fibers : (∑ index ∈ points.image (fun point => projection point.1),
      fragmentAlternations right (fiber projection index points)) =
      fragmentAlternations right (fiber projection 0 points) := by
    apply Finset.sum_eq_single 0
    · intro index present nonzero
      apply fragmentAlternations_constant _ _ exception
      intro point member
      obtain ⟨present,same⟩ := Finset.mem_filter.mp member
      rcases cells point present with zero | singleton
      · exact (nonzero (same.symm.trans zero)).elim
      · exact singleton
    · intro absent
      have empty : fiber projection 0 points = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro point member
        obtain ⟨present,zero⟩ := Finset.mem_filter.mp member
        exact absent (Finset.mem_image.mpr ⟨point,present,zero⟩)
      rw [empty,fragmentAlternations_empty]
  have localBound := fragment_event_charge valid projection exception different cells
  have charged : (points.filter (fun point => point.1 = exception)).card ≤
      (points.filter (fun point => ¬ projection point.1 = 0)).card := by
    apply Finset.card_le_card
    intro point member
    obtain ⟨present,same⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨present,by simpa only [same] using different⟩
  have partition := Finset.card_filter_add_card_filter_not (s := points)
    (fun point => projection point.1 = 0)
  change eventCount points (DownUpAt points projection) +
    fragmentAlternations left (project projection points) +
    (∑ index ∈ points.image (fun point => projection point.1),
      fragmentAlternations right (fiber projection index points)) ≤ _
  rw [projected,fibers]
  change fragmentAlternations right (fiber projection 0 points) ≤
    (points.filter (fun point => projection point.1 = 0)).card at recursive
  omega

theorem sparseKey_nonnegative (index : Nat) : 0 ≤ sparseKey index := by
  cases index with
  | zero => rfl
  | succ index => exact le_of_lt (pow_pos (by decide) _)

theorem fragment_midpoint_congr {a c b : Nat} (same : a = c) (first : a ≤ b)
    (last : c ≤ b) (points : Finset Point) :
    fragmentAlternations (DepthTree.midpoint a b first) points =
      fragmentAlternations (DepthTree.midpoint c b last) points := by
  subst c
  rfl

theorem sparse_midpoint_fragments (levels top : Nat) (fits : 2^levels ≤ top)
    (points : Finset Point) (valid : Instance points)
    (support : ∀ point ∈ points, ∃ index < levels+1, point.1 = sparseKey index) :
    fragmentAlternations (DepthTree.midpoint (top-2^levels) (top-1) (by
      have positive : 0 < (2:Nat)^levels := pow_pos (by decide) _
      omega)) points ≤ points.card := by
  induction levels generalizing points with
  | zero =>
      change fragmentAlternations (DepthTree.midpoint (top-1) (top-1) _) points ≤ points.card
      rw [DepthTree.midpoint,dif_pos rfl]
      exact Nat.zero_le _
  | succ levels ih =>
      have positive : 0 < (2:Nat)^levels := pow_pos (by decide) _
      have large : 2^levels*2 ≤ top := by simpa only [pow_succ] using fits
      have unequal : top-2^(levels+1) ≠ top-1 := by rw [pow_succ]; omega
      have middle : (top-2^(levels+1)+(top-1))/2 = top-2^levels-1 := by
        rw [pow_succ]
        omega
      have next : (top-2^(levels+1)+(top-1))/2+1 = top-2^levels := by rw [middle]; omega
      have projection : coarsen ((top-1)+1)
          (((top-2^(levels+1)+(top-1))/2)+1) = fun key => key / sparseKey (levels+1) := by
        funext key
        simp only [coarsen,next,sparseKey]
        congr 2
        omega
      have exceptional : coarsen ((top-1)+1)
          (((top-2^(levels+1)+(top-1))/2)+1) (sparseKey (levels+1)) = 1 := by
        rw [projection]
        exact Int.ediv_self (ne_of_gt (pow_pos (by decide) _))
      have small : ∀ index < levels+1, sparseKey index / sparseKey (levels+1) = 0 := by
        intro index below
        exact Int.ediv_eq_zero_of_lt (sparseKey_nonnegative index) (sparseKey_increasing below)
      have cells : ∀ point ∈ points, coarsen ((top-1)+1)
          (((top-2^(levels+1)+(top-1))/2)+1) point.1 = 0 ∨ point.1 = sparseKey (levels+1) := by
        intro point member
        obtain ⟨index,below,same⟩ := support point member
        by_cases last : index = levels+1
        · exact Or.inr (by simpa only [last] using same)
        · exact Or.inl (by rw [projection,same]; exact small index (by omega))
      rw [DepthTree.midpoint,dif_neg unequal]
      apply fragmentAlternations_singleton_split _ _ _ _ points valid (sparseKey (levels+1)) exceptional cells
      rw [fragment_midpoint_congr next _ (by omega)]
      simp only [next]
      apply ih (by omega) _ (instance_fiber valid _ 0)
      intro point member
      obtain ⟨present,zero⟩ := Finset.mem_filter.mp member
      obtain ⟨index,below,same⟩ := support point present
      refine ⟨index,?_,same⟩
      have notLast : index ≠ levels+1 := by
        intro last
        have one := exceptional
        rw [next,← last,← same] at one
        omega
      omega

end ChaCha.Separation
