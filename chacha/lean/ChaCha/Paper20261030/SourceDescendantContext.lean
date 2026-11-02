import ChaCha.Paper20261030.SourceFingerExtension
import ChaCha.Paper20261030.PackedContext

set_option autoImplicit false

/-! A successful downward route supplies its exact intervening context.
This is proof-only geometry; the controller does not receive the context. -/

namespace ChaCha.Paper20261030.SourcePositions

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ : Type*}

theorem descend_context {before after : Cursor α ρ} {path : List Bool}
    (reached : descend before path = some after) :
    ∃ inside : List (Frame α ρ), inside.length = path.length ∧
      before.focus = plug after.focus inside ∧ after.ancestors = inside ++ before.ancestors := by
  induction path generalizing before with
  | nil =>
    have same : before = after := Option.some.inj reached
    subst before
    exact ⟨[],rfl,rfl,rfl⟩
  | cons side rest ih =>
    rcases before with ⟨focus,outside⟩
    cases focus with
    | leaf => cases side <;> simp [descend,navigate] at reached
    | fork record left right =>
      cases side
      · obtain ⟨inside,length,focus,ancestors⟩ :=
          ih (before := ⟨left,.left record right::outside⟩) reached
        refine ⟨inside ++ [.left record right],by simp [length],?_,?_⟩
        · simp only [plug_append,plug]
          exact congrArg (fun tree => Source.fork record tree right) focus
        · simpa only [List.append_assoc,List.singleton_append] using ancestors
      · obtain ⟨inside,length,focus,ancestors⟩ :=
          ih (before := ⟨right,.right left record::outside⟩) reached
        refine ⟨inside ++ [.right left record],by simp [length],?_,?_⟩
        · simp only [plug_append,plug]
          exact congrArg (fun tree => Source.fork record left tree) focus
        · simpa only [List.append_assoc,List.singleton_append] using ancestors

theorem descend_proper_context {before after : Cursor α ρ} {path : List Bool}
    (reached : descend before path = some after) (nonempty : path ≠ []) :
    ∃ inside : List (Frame α ρ), inside ≠ [] ∧
      before.focus = plug after.focus inside ∧ after.ancestors = inside ++ before.ancestors := by
  obtain ⟨inside,length,focus,ancestors⟩ := descend_context reached
  refine ⟨inside,?_,focus,ancestors⟩
  intro empty
  apply nonempty
  exact List.length_eq_zero_iff.mp (by simpa only [empty,List.length_nil] using length.symm)

end ChaCha.Paper20261030.SourcePositions
