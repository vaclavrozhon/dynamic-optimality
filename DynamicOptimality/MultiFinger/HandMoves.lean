import DynamicOptimality.MultiFinger.HandMovesAdd
import DynamicOptimality.MultiFinger.HandMovesMarkers

/-! # One actual static finger move changes at most two hand endpoints

A destination is retained before the old position is released. The common
intermediate mark set contains both endpoints. Multiplicity and the
permanent reference-root mark are handled by the exact occupied-position
predicate, so no update removes a mark still used by another finger.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

variable {α : Type*}

theorem Configuration.update_mark_union {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (index : Fin count)
    (next : Pointer.Cursor α) (valid : next.tree = reference)
    {first last : α} (firstKey : (state.finger index).focus.rootKey = some first)
    (lastKey : next.focus.rootKey = some last) :
    ∀ key,
      (state.marked key = true ∨ key = last) ↔
      ((state.update index next valid).marked key = true ∨ key = first) := by
  classical
  intro key
  rw [state.marked_iff, Configuration.marked_iff]
  constructor
  · rintro ((root | ⟨other, found⟩) | equal)
    · exact Or.inl (Or.inl root)
    · by_cases same : other = index
      · subst other
        exact Or.inr (Option.some.inj (firstKey.symm.trans found)).symm
      · exact Or.inl (Or.inr ⟨other, by
          simpa only [update, Function.update_of_ne same] using found⟩)
    · subst key
      exact Or.inl (Or.inr ⟨index, by simpa only [update, Function.update_self] using lastKey⟩)
  · rintro ((root | ⟨other, found⟩) | equal)
    · exact Or.inl (Or.inl root)
    · by_cases same : other = index
      · subst other
        simp only [update, Function.update_self] at found
        exact Or.inr (Option.some.inj (lastKey.symm.trans found)).symm
      · exact Or.inl (Or.inr ⟨other, by
          simpa only [update, Function.update_of_ne same] using found⟩)
    · subst key
      exact Or.inl (Or.inr ⟨index, firstKey⟩)

private theorem root_exists {tree : RawTree α} (nonempty : tree ≠ .empty) :
    ∃ key, tree.rootKey = some key := by
  cases tree with
  | empty => exact False.elim (nonempty rfl)
  | node left key right => exact ⟨key, rfl⟩

/-- A legal edge move of one live persistent finger changes the exact
compressed source hand by at most two endpoint edits. The distinctness
assumption prevents one key mark from naming multiple source vertices. -/
theorem Step.hand_endpointEdits {reference : RawTree α} {count : Nat}
    {before after : Configuration reference count} (step : Step before after)
    (distinct : reference.inorder.Nodup) (live : before.Live) :
    ∃ edits ≤ 2,
      Hand.EndpointEdits (Hand.compress before.marked reference)
        (Hand.compress after.marked reference) edits := by
  classical
  cases step with
  | move index next actual valid =>
      have endLive := (Step.move before index next actual valid).live live
      have nextLive : next.focus ≠ .empty := by
        simpa only [Configuration.update, Function.update_self] using endLive index
      obtain ⟨first, firstKey⟩ := root_exists (live index)
      obtain ⟨last, lastKey⟩ := root_exists nextLive
      have edge := edge_of_same_tree actual ((before.valid index).trans valid.symm)
      have adjacency := Hand.adjacent_of_edge edge firstKey lastKey
      rw [before.valid index] at adjacency
      have firstMarked := before.marked_finger index firstKey
      have lastMarked : (before.update index next valid).marked last = true := by
        apply Configuration.marked_finger _ index
        simpa only [Configuration.update, Function.update_self] using lastKey
      obtain ⟨frontCount, frontBound, frontTrace⟩ :=
        (adjacency.add_mark distinct before.marked firstMarked).endpoint.trace
      obtain ⟨backCount, backBound, backTrace⟩ :=
        (adjacency.symm.add_mark distinct (before.update index next valid).marked lastMarked).endpoint.trace
      have common : Hand.addMark before.marked last =
          Hand.addMark (before.update index next valid).marked first := by
        funext key
        apply Bool.eq_iff_iff.mpr
        simp only [Hand.addMark, Bool.or_eq_true, decide_eq_true_eq]
        exact before.update_mark_union index next valid firstKey lastKey key
      rw [common] at frontTrace
      exact ⟨frontCount+backCount, by omega, frontTrace.append backTrace.symm⟩

end DynamicOptimality.MultiFinger
