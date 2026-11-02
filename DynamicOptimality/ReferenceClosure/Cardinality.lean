import DynamicOptimality.ReferenceClosure.Geometry
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!+# Cost of reference closure

Rows retain their original time coordinate. The construction keeps every
original point and adds at most one fewer point than the original size of
each nonempty row. Thus its total geometric cost is at most doubled.
-/

namespace DynamicOptimality.Geometry.ReferenceClosure

open Splay.Tree

theorem subset_closePoints {lo hi : Nat} (tree : BST lo hi) (points : Finset Point) :
    points ⊆ closePoints tree points := by
  intro p hp
  apply (closePoints_mem tree points p).mpr
  by_cases outside : p.1 < lo ∨ hi ≤ p.1
  · exact Or.inl ⟨hp, outside⟩
  · exact Or.inr (selected_subset_row tree _ ((mem_selected tree _).mpr
      ⟨mem_rowAt.mpr hp, by omega, by omega⟩))

theorem closePoints_mem_bounded {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) (p : Point) :
    p ∈ closePoints tree points ↔ p.1 ∈ row tree (rowAt points p.2) := by
  rw [closePoints_mem]
  constructor
  · rintro (⟨old, outside⟩ | closed)
    · have := bounded p old
      omega
    · exact closed
  · exact Or.inr

theorem rowAt_closePoints {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) (time : Int) :
    rowAt (closePoints tree points) time = row tree (rowAt points time) := by
  ext key
  exact mem_rowAt.trans (closePoints_mem_bounded tree bounded (key,time))

theorem closePoints_bounded {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) :
    ∀ p ∈ closePoints tree points, lo ≤ p.1 ∧ p.1 < hi := by
  intro p hp
  exact row_bounded tree _ _ ((closePoints_mem_bounded tree bounded p).mp hp)

theorem closePoints_times {lo hi : Nat} (tree : BST lo hi) (points : Finset Point) :
    (closePoints tree points).image Prod.snd = points.image Prod.snd := by
  apply Finset.Subset.antisymm
  · intro time member
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp member
    rcases (closePoints_mem tree points p).mp hp with ⟨old, _⟩ | closed
    · exact Finset.mem_image_of_mem _ old
    · obtain ⟨key, hk⟩ := (row_nonempty_iff tree _).mp ⟨p.1, closed⟩
      have old := mem_rowAt.mp ((mem_selected tree _).mp hk).1
      exact Finset.mem_image.mpr ⟨(key,p.2), old, rfl⟩
  · exact Finset.image_subset_image (subset_closePoints tree points)

theorem card_eq_sum_rowAt (points : Finset Point) :
    points.card = ∑ time ∈ points.image Prod.snd, (rowAt points time).card := by
  rw [Finset.card_eq_sum_card_image Prod.snd points]
  apply Finset.sum_congr rfl
  intro time _
  symm
  apply Finset.card_image_of_injOn
  intro p hp q hq equal
  have pt := (Finset.mem_filter.mp hp).2
  have qt := (Finset.mem_filter.mp hq).2
  exact Prod.ext equal (pt.trans qt.symm)

theorem selected_rowAt {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) (time : Int) :
    selected tree (rowAt points time) = rowAt points time := by
  apply Finset.filter_eq_self.mpr
  intro key member
  exact bounded (key,time) (mem_rowAt.mp member)

/-- The exact row-count improvement over the factor-two total bound. -/
theorem closePoints_card_add_rows_le {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) :
    (closePoints tree points).card + (points.image Prod.snd).card ≤ 2 * points.card := by
  rw [card_eq_sum_rowAt (closePoints tree points), closePoints_times]
  rw [card_eq_sum_rowAt points, Finset.mul_sum]
  have bound : ∀ time ∈ points.image Prod.snd,
      (rowAt (closePoints tree points) time).card + 1 ≤ 2 * (rowAt points time).card := by
    intro time member
    obtain ⟨p, hp, eq⟩ := Finset.mem_image.mp member
    have nonempty : (rowAt points time).Nonempty :=
      ⟨p.1, mem_rowAt.mpr (by simpa [← eq] using hp)⟩
    have positive := Finset.card_pos.mpr nonempty
    rw [rowAt_closePoints tree bounded]
    have rowBound := row_card_le tree (rowAt points time)
    rw [selected_rowAt tree bounded] at rowBound
    omega
  have total := Finset.sum_le_sum bound
  simpa [Finset.sum_add_distrib] using total

theorem closePoints_card_le {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) :
    (closePoints tree points).card ≤ 2 * points.card := by
  have := closePoints_card_add_rows_le tree bounded
  omega

theorem closed_rows {lo hi : Nat} (tree : BST lo hi) {points : Finset Point}
    (bounded : ∀ p ∈ points, lo ≤ p.1 ∧ p.1 < hi) (time : Int) :
    row tree (rowAt (closePoints tree points) time) = rowAt (closePoints tree points) time := by
  rw [rowAt_closePoints tree bounded, row_idempotent]

end DynamicOptimality.Geometry.ReferenceClosure
