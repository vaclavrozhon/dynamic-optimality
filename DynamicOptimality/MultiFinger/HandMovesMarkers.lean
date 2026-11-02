import DynamicOptimality.MultiFinger.StaticEdges

/-! # Actual occupied positions, with a permanent mark at the reference root -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

variable {α : Type*}

noncomputable def Configuration.marked {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (key : α) : Bool := by
  classical
  exact decide (reference.rootKey = some key ∨
    ∃ index, (state.finger index).focus.rootKey = some key)

theorem Configuration.marked_iff {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (key : α) :
    state.marked key = true ↔ reference.rootKey = some key ∨
      ∃ index, (state.finger index).focus.rootKey = some key := by
  classical
  simp only [marked, decide_eq_true_eq]

theorem Configuration.marked_finger {reference : RawTree α} {count : Nat}
    (state : Configuration reference count) (index : Fin count) {key : α}
    (found : (state.finger index).focus.rootKey = some key) : state.marked key = true :=
  (state.marked_iff key).mpr (Or.inr ⟨index, found⟩)

end DynamicOptimality.MultiFinger
