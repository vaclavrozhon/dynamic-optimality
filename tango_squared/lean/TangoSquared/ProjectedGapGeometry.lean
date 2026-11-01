import TangoSquared.RunOccurrences
import TangoSquared.GapRecords

/-!
# Selecting the delayed payment in an actual projected run gap

These are order/list statements about the original fine labels. They provide
the exact earliest-trigger prefix accepted by `projected_delayed_record`.
-/

namespace TangoSquared.ProjectedGapGeometry

variable {α C : Type*} [LinearOrder α] [DecidableEq C]

def Opposite (coarse : α → C) (y p z : α) : Prop :=
  coarse z ≠ coarse y ∧ ((z < y ∧ y < p) ∨ (p < y ∧ y < z))

instance (coarse : α → C) (y p z : α) : Decidable (Opposite coarse y p z) :=
  inferInstanceAs (Decidable (coarse z ≠ coarse y ∧ ((z < y ∧ y < p) ∨ (p < y ∧ y < z))))

/-- An outside-side bit disagrees with the micro direction precisely for an
opposite-side trigger. Equal keys are excluded explicitly. -/
theorem opposite_iff_direction_ne (y p z : α) (micro : y ≠ p) (outside : z ≠ y) :
    ((z < y ∧ y < p) ∨ (p < y ∧ y < z)) ↔ decide (y < z) ≠ decide (y < p) := by
  rcases lt_or_gt_of_ne micro with hyp | hpy
  · have hnpy : ¬ p < y := not_lt.mpr (le_of_lt hyp)
    have hyzne : y ≠ z := Ne.symm outside
    rcases lt_or_gt_of_ne hyzne with hyz | hzy
    · simp [hyp, hnpy, hyz, not_lt.mpr (le_of_lt hyz)]
    · simp [hyp, hnpy, hzy, not_lt.mpr (le_of_lt hzy)]
  · have hnyp : ¬ y < p := not_lt.mpr (le_of_lt hpy)
    have hyzne : y ≠ z := Ne.symm outside
    rcases lt_or_gt_of_ne hyzne with hyz | hzy
    · simp [hpy, hnyp, hyz, not_lt.mpr (le_of_lt hyz)]
    · simp [hpy, hnyp, hzy, not_lt.mpr (le_of_lt hzy)]

omit [DecidableEq C] in
/-- Before the first opposite query, every other-cell query lies on the original
micro side. This conclusion uses literal fine-label comparisons. -/
theorem original_side (coarse : α → C) (y p z : α) (micro : y ≠ p)
    (outside : coarse z ≠ coarse y) (not_opposite : ¬ Opposite coarse y p z) :
    (y < p ∧ y < z) ∨ (p < y ∧ z < y) := by
  have hzy : z ≠ y := fun h => outside (congrArg coarse h)
  rcases lt_or_gt_of_ne micro with hyp | hpy
  · refine Or.inl ⟨hyp, ?_⟩
    by_contra hn
    have hzy' : z < y := lt_of_le_of_ne (le_of_not_gt hn) hzy
    exact not_opposite ⟨outside, Or.inl ⟨hzy', hyp⟩⟩
  · refine Or.inr ⟨hpy, ?_⟩
    by_contra hn
    have hyz : y < z := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hzy)
    exact not_opposite ⟨outside, Or.inr ⟨hpy, hyz⟩⟩

/-- An opposite excursion produces an exact chronological trigger, with all
earlier fine-label queries satisfying the retained-record condition. -/
theorem first_opposite_split (coarse : α → C) (y p : α) (gap : List α)
    (micro : y ≠ p)
    (retained : ∀ z ∈ gap, coarse z = coarse y → z = p)
    (hit : ∃ x ∈ gap, Opposite coarse y p x) :
    ∃ earlier x later, gap = earlier ++ x :: later ∧ Opposite coarse y p x ∧
      (∀ z ∈ earlier, z = p ∨ (coarse z ≠ coarse y ∧
        ((y < p ∧ y < z) ∨ (p < y ∧ z < y)))) := by
  obtain ⟨earlier, x, later, hgap, hopposite, hfirst⟩ :=
    Witnesses.first_hit_split (Opposite coarse y p) gap hit
  refine ⟨earlier, x, later, hgap, hopposite, ?_⟩
  intro z hz
  by_cases hsame : coarse z = coarse y
  · left
    apply retained z _ hsame
    rw [hgap]
    exact List.mem_append.mpr (Or.inl hz)
  · exact Or.inr ⟨hsame, original_side coarse y p z micro hsame (hfirst z hz)⟩

end TangoSquared.ProjectedGapGeometry
