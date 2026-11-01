import Splay.Accounting.FullOrderSegment

namespace Splay.Accounting

open Splay.Lazy

/-- A subsequence of a duplicate-free order is exactly the membership filter.
This retains the original order without assuming that the source is unbroken. -/
theorem sublist_eq_filter_mem {α : Type*} [DecidableEq α] {inside whole : List α}
    (sublist : inside.Sublist whole) (distinct : whole.Nodup) :
    inside = whole.filter (fun element => decide (element ∈ inside)) := by
  classical
  let keep := fun element => decide (element ∈ inside)
  have self : inside.filter keep = inside := List.filter_eq_self.mpr (by simp [keep])
  have filtered : inside.Sublist (whole.filter keep) := by
    simpa only [self] using sublist.filter keep
  have filteredDistinct : (whole.filter keep).Nodup := distinct.filter keep
  have subset : (whole.filter keep).toFinset ⊆ inside.toFinset := by
    intro element member
    simpa [keep] using (List.mem_filter.mp (List.mem_toFinset.mp member)).2
  have lengthLe : (whole.filter keep).length ≤ inside.length := by
    calc
      (whole.filter keep).length = (whole.filter keep).toFinset.card :=
        (List.toFinset_card_of_nodup filteredDistinct).symm
      _ ≤ inside.toFinset.card := Finset.card_le_card subset
      _ ≤ inside.length := List.toFinset_card_le inside
  exact filtered.eq_of_length (Nat.le_antisymm filtered.length_le lengthLe)

/-- A consecutive candidate triple stays consecutive in any source
subsequence that contains it, even if that source has gaps elsewhere. -/
theorem _root_.Splay.Lazy.IsSegment.in_sublist {α : Type*} {candidates source whole : List α}
    (segment : IsSegment candidates whole) (sourceSublist : source.Sublist whole)
    (distinct : whole.Nodup) (contained : candidates ⊆ source) :
    IsSegment candidates source := by
  classical
  have sourceEq := sublist_eq_filter_mem sourceSublist distinct
  obtain ⟨front, back, wholeEq⟩ := segment
  have kept : candidates.filter (fun element => decide (element ∈ source)) = candidates :=
    List.filter_eq_self.mpr (by intro element member; simpa using contained member)
  refine ⟨front.filter (fun element => decide (element ∈ source)),
    back.filter (fun element => decide (element ∈ source)), ?_⟩
  calc
    source = whole.filter (fun element => decide (element ∈ source)) := sourceEq
    _ = _ := by rw [wholeEq, List.filter_append, List.filter_append, kept]

end Splay.Accounting
