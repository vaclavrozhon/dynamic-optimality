import TangoSquared.Paper20261030.ForestConnectorLayout

/-! The one-piece case of forest assembly. A physical forest instruction
on its present color is exactly one shared-tree instruction. Reads of an
absent color are reads of an absent finger register.
-/

namespace TangoSquared.Paper20261030.ForestConnector

open ColoredStorage SourcePointer SourcePositions

variable {α ρ C σ : Type*} [DecidableEq C]

def Scoped (source : ForestLocalProgram.Program σ C ρ) (state : σ)
    (forest : ProjectionForest.State C α ρ) (layout : Source C Unit) : Prop :=
  ∀ q ∈ (program source state).targets, ∀ current, forest q = some current → q ∈ colors layout

theorem move_single (q : C) (before after : Cursor α (List ρ)) (action : DynamicOptimality.LocalProgram.Move) :
    MultiSourceProgram.moveResult (single q before) q action before after = single q after := by
  apply congrArg₂ MultiSourceProgram.Configuration.mk
  · rfl
  · funext other
    by_cases same : other = q
    · subst other; simp [MultiSourceProgram.moveResult,single]
    · simp [MultiSourceProgram.moveResult,single,same]

theorem write_single (q : C) (current : Cursor α (List ρ)) (fresh : List ρ) :
    MultiSourceProgram.writeResult (single q current) current fresh = single q ⟨current.focus.setRoot fresh,current.ancestors⟩ := rfl

theorem single_step (source : ForestLocalProgram.Program σ C ρ) {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : ForestLocalProgram.Step source state before next after entry)
    (q : C) (current : Cursor α (List ρ)) (present : before q = some current)
    (scopeReady : Scoped source state before (.leaf q ())) :
    ∃ target, after q = some target ∧ MultiSourceProgram.Step (program source) state (single q current) next (single q target) entry := by
  have onlySelected : ∀ selected ∈ (program source state).targets, ∀ cursor, before selected = some cursor → selected = q := by
    intro selected member cursor location
    simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using scopeReady selected member cursor location
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead selected
    have different : selected ≠ q := by intro equal; subst selected; rw [present] at absent; cases absent
    exact ⟨current,present,.readNone (finger := selected) (by simp only [program,instruction]) (by simp only [single,different,if_false])⟩
  | readSome instruction location =>
    rename_i nextRead selected cursor
    have equal : selected = q := onlySelected selected (by simp [program,instruction,MultiSourceProgram.Instruction.targets]) cursor location
    subst selected
    have cursorEqual : cursor = current := Option.some.inj (location.symm.trans present)
    subst cursor
    exact ⟨current,present,.readSome (current := current) (position := address current)
      (by simp only [program,instruction]) (by simp only [single,ite_true]) (locate_cursor current)⟩
  | nav instruction location moved =>
    rename_i selected cursor target action
    have equal : selected = q := onlySelected selected (by simp [program,instruction,MultiSourceProgram.Instruction.targets]) cursor location
    subst selected
    have cursorEqual : cursor = current := Option.some.inj (location.symm.trans present)
    subst cursor
    have actual := MultiSourceProgram.Step.nav (program := program source) (state := state) (next := next) (finger := q) (action := action)
      (by simp only [program,instruction]) (show (single q current).fingers q = some (address current) by simp only [single,ite_true])
      (locate_cursor current) moved
    exact ⟨target,Function.update_self _ _ _,by simpa only [move_single] using actual⟩
  | write instruction location =>
    rename_i selected cursor fresh
    have equal : selected = q := onlySelected selected (by simp [program,instruction,MultiSourceProgram.Instruction.targets]) cursor location
    subst selected
    have cursorEqual : cursor = current := Option.some.inj (location.symm.trans present)
    subst cursor
    have actual := MultiSourceProgram.Step.write (program := program source) (state := state) (next := next) (finger := q) (fresh := fresh)
      (by simp only [program,instruction]) (show (single q current).fingers q = some (address current) by simp only [single,ite_true])
      (locate_cursor current)
    exact ⟨_,Function.update_self _ _ _,by simpa only [write_single] using actual⟩

theorem step_target (source : ForestLocalProgram.Program σ C ρ) {state next : σ}
    {before after : ProjectionForest.State C α ρ} {entry}
    (execution : ForestLocalProgram.Step source state before next after entry) :
    ∃ q, (program source state).targets = [q] ∧ ∀ other, other ≠ q → before other = after other := by
  cases execution with
  | readNone instruction absent =>
    rename_i nextRead q
    exact ⟨q,by simp only [program,instruction,MultiSourceProgram.Instruction.targets],fun _ _ => rfl⟩
  | readSome instruction present =>
    rename_i nextRead q cursor
    exact ⟨q,by simp only [program,instruction,MultiSourceProgram.Instruction.targets],fun _ _ => rfl⟩
  | nav instruction present moved =>
    rename_i q current target action
    refine ⟨q,by simp only [program,instruction,MultiSourceProgram.Instruction.targets],?_⟩
    intro other different
    simp only [Function.update_of_ne different]
  | write instruction present =>
    rename_i q cursor fresh
    refine ⟨q,by simp only [program,instruction,MultiSourceProgram.Instruction.targets],?_⟩
    intro other different
    simp only [Function.update_of_ne different]

end TangoSquared.Paper20261030.ForestConnector
