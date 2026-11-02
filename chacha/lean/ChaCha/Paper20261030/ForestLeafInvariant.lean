import ChaCha.Paper20261030.ForestProgramComposition
import ChaCha.Paper20261030.VirtualCursorSize

/-! Every actual forest-program prefix preserves each color's leaf
word, including inside metadata maintenance. A virtual projection with
at most two leaves therefore keeps at most one ancestor and at most
three vertices throughout an execution. Record-capacity bounds are a
distinct obligation; leaf count alone does not bound record lists.
-/

namespace ChaCha.Paper20261030.ForestLocalProgram

open ColoredStorage SourcePointer

variable {α ρ C σ : Type*} [DecidableEq C]

def leafWord (forest : ProjectionForest.State C α ρ) (q : C) : Option (List α) :=
  (forest q).map (fun current => current.tree.shape.leaves)

theorem Step.leaves {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : Step source state before next after entry) (q : C) : leafWord before q = leafWord after q := by
  cases execution with
  | readNone | readSome => rfl
  | nav instruction present moved =>
    rename_i selected current target action
    by_cases same : q = selected
    · subst q
      simp only [leafWord,Function.update_self,present,Option.map_some]
      exact congrArg some (SourceLocalProgram.navigate_sound moved).leaves
    · simp only [leafWord,Function.update_of_ne same]
  | write instruction present =>
    rename_i selected current fresh
    by_cases same : q = selected
    · subst q
      simp only [leafWord,Function.update_self,present,Option.map_some]
      exact congrArg some (SourcePointer.Step.write current.focus fresh current.ancestors).leaves
    · simp only [leafWord,Function.update_of_ne same]

theorem Steps.leaves {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : Steps source state before next after reads cost) (q : C) : leafWord before q = leafWord after q := by
  induction execution with
  | nil => rfl
  | next first rest ih => exact (first.leaves q).trans ih

theorem Run.leaves {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost}
    (execution : Run source state before next after reads cost) (q : C) : leafWord before q = leafWord after q := by
  induction execution with
  | halt => rfl
  | next first rest ih => exact (first.leaves q).trans ih

def Small (bound : Nat) (forest : ProjectionForest.State C α ρ) (q : C) : Prop :=
  ∀ current, forest q = some current → current.tree.shape.leaves.length ≤ bound

theorem small_of_leafWord {bound : Nat} {before after : ProjectionForest.State C α ρ} {q : C}
    (same : leafWord before q = leafWord after q) (small : Small bound before q) : Small bound after q := by
  intro current present
  cases original : before q with
  | none => simp only [leafWord,original,present,Option.map_none,Option.map_some,reduceCtorEq] at same
  | some old =>
    have equal : old.tree.shape.leaves = current.tree.shape.leaves := by
      simpa only [leafWord,original,present,Option.map_some,Option.some.injEq] using same
    rw [← equal]
    exact small old original

theorem Steps.small {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost bound q}
    (execution : Steps source state before next after reads cost) (small : Small bound before q) : Small bound after q :=
  small_of_leafWord (execution.leaves q) small

theorem Run.small {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost bound q}
    (execution : Run source state before next after reads cost) (small : Small bound before q) : Small bound after q :=
  small_of_leafWord (execution.leaves q) small

theorem Steps.virtual_depth {source : Program σ C ρ} {state next : σ}
    {before after : ProjectionForest.State C α ρ} {reads cost q}
    (execution : Steps source state before next after reads cost) (small : Small 2 before q)
    (current : Cursor α (List ρ)) (present : after q = some current) : current.ancestors.length ≤ 1 :=
  virtual_cursor_depth current (execution.small small current present)

end ChaCha.Paper20261030.ForestLocalProgram
