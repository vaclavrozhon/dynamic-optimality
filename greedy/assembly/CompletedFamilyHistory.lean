import ConcreteHistoryEdits

/-!
The retrospective family history is read from the actual conversion state.
Earlier times use that same state, so future growth entries are already
present in the proof-only prefix. No extra all-tickets containment premise
is needed: after conversion the actual split/delete/rebase/move program
is a closed-family edit run.
-/

namespace GreedyMerge.HistoryProcess

open OrderedBlocks FrozenHistory GreedyForest

def completedBlocks (conversion : ℕ) (actual : ℕ → List Frozen) (time : ℕ) :
    List Frozen := actual (max conversion time)

noncomputable def completedView (family conversion : ℕ)
    (actual : ℕ → List Frozen) (time : ℕ) : Family ℕ :=
  familyView family (completedBlocks conversion actual time)

theorem completedBlocks_before (conversion time : ℕ) (actual : ℕ → List Frozen)
    (before : time ≤ conversion) :
    completedBlocks conversion actual time = actual conversion := by
  simp only [completedBlocks, max_eq_left before]

theorem completedBlocks_after (conversion time : ℕ) (actual : ℕ → List Frozen)
    (after : conversion ≤ time) :
    completedBlocks conversion actual time = actual time := by
  simp only [completedBlocks, max_eq_right after]

/-- Each completed step is either literally stationary or an actual
closed-family program after conversion. -/
theorem completedBlocks_step (conversion : ℕ) (actual : ℕ → List Frozen)
    (steps : ∀ time, conversion ≤ time → Run (actual time) (actual (time + 1)))
    (time : ℕ) :
    Run (completedBlocks conversion actual time)
      (completedBlocks conversion actual (time + 1)) := by
  by_cases after : conversion ≤ time
  · rw [completedBlocks_after _ _ _ after,
      completedBlocks_after _ _ _ (by omega)]
    exact steps time after
  · rw [completedBlocks_before _ _ _ (by omega),
      completedBlocks_before _ _ _ (by omega)]
    exact .nil _

theorem completedBlocks_from_conversion (conversion : ℕ) (actual : ℕ → List Frozen)
    (steps : ∀ time, conversion ≤ time → Run (actual time) (actual (time + 1)))
    (time : ℕ) :
    Run (actual conversion) (completedBlocks conversion actual time) := by
  induction time with
  | zero => simpa only [completedBlocks, Nat.max_zero] using Run.nil (actual conversion)
  | succ time ih => exact ih.trans (completedBlocks_step conversion actual steps time)

theorem completedView_refines (family conversion : ℕ) (actual : ℕ → List Frozen)
    (steps : ∀ time, conversion ≤ time → Run (actual time) (actual (time + 1)))
    (time : ℕ) :
    Refines (completedView family conversion actual (time + 1))
      (completedView family conversion actual time) :=
  (completedBlocks_step conversion actual steps time).refines family

/-- The ordered, partitioned and unique-straddler interfaces follow from
the actual conversion invariant and actual subsequent history edits. -/
theorem completedView_geometry (family conversion : ℕ) (actual : ℕ → List Frozen)
    (initial : Valid (actual conversion))
    (steps : ∀ time, conversion ≤ time → Run (actual time) (actual (time + 1)))
    (time cut : ℕ) :
    OrderedFamily (completedView family conversion actual time) ∧
    Partitioned (completedView family conversion actual time) ∧
    UniqueStraddler (fun joined => decide (cut ≤ joined))
      (completedView family conversion actual time) := by
  have valid := (completedBlocks_from_conversion conversion actual steps time).valid initial
  have ordered := family_ordered family _ valid
  exact ⟨ordered, ordered_partitioned _ ordered, orderedFamily_uniqueStraddler _ _ ordered⟩

/-- When the conversion state consists of its actual single frozen block,
the completed prefix is exactly the full eventual membership-ticket set. -/
theorem completedView_growing_prefix (initial : Frozen) (conversion time : ℕ)
    (actual : ℕ → List Frozen) (atConversion : actual conversion = [initial])
    (before : time ≤ conversion) :
    completedView initial.family conversion actual time = {joins initial} := by
  rw [completedView, completedBlocks_before _ _ _ before, atConversion]
  simp [familyView]

end GreedyMerge.HistoryProcess

#print axioms GreedyMerge.HistoryProcess.completedView_refines
#print axioms GreedyMerge.HistoryProcess.completedView_geometry
