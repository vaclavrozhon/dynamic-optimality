import TangoSquared.Paper20261030.MultiSourceProgram

/-! Actual local instructions preserve valid physical finger positions.
Rotation updates are determined by the reached local shape; writes alter
records but preserve every vertex position.
-/

namespace TangoSquared.Paper20261030.SourcePositions

open ColoredStorage SourcePointer

variable {α ρ : Type*}

theorem context_presence {before after : Source α ρ} (outside : List (Frame α ρ))
    (preserved : ∀ position, (recordAt after position).isSome = (recordAt before position).isSome)
    (position : List Bool) :
    (recordAt (plug after outside) position).isSome = (recordAt (plug before outside) position).isSome := by
  induction outside generalizing before after with
  | nil => exact preserved position
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      apply ih
      intro place
      cases place with
      | nil => rfl
      | cons first tail => cases first with
        | false => exact preserved tail
        | true => rfl
    | right sibling record =>
      apply ih
      intro place
      cases place with
      | nil => rfl
      | cons first tail => cases first with
        | false => rfl
        | true => exact preserved tail

theorem setRoot_presence (focus : Source α ρ) (fresh : ρ) (outside : List (Frame α ρ)) (position : List Bool) :
    (recordAt (plug (focus.setRoot fresh) outside) position).isSome = (recordAt (plug focus outside) position).isSome := by
  apply context_presence
  intro place
  cases focus <;> cases place
  all_goals try rfl
  rename_i first rest
  cases first <;> rfl

theorem valid_of_presence {tree : Source α ρ} {position : List Bool}
    (present : (recordAt tree position).isSome = true) : ∃ current, locate tree position = some current := by
  rw [← locate_record] at present
  cases reached : locate tree position with
  | none => simp only [reached,Option.map_none,Option.isSome_none,Bool.false_eq_true] at present
  | some current => exact ⟨current,rfl⟩

end TangoSquared.Paper20261030.SourcePositions

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions
open DynamicOptimality.LocalProgram (Move)

variable {α ρ F σ : Type*} [DecidableEq F]

theorem navigate_transport (action : Move) {before after : Cursor α ρ}
    (moved : SourceLocalProgram.navigate action before = some after)
    (position : List Bool) (current : Cursor α ρ) (reached : locate before.tree position = some current) :
    ∃ target, locate after.tree (transport action before position) = some target := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | left => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork => cases Option.some.inj moved; exact ⟨current,reached⟩
  | right => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork => cases Option.some.inj moved; exact ⟨current,reached⟩
  | up => cases outside with
    | nil => simp [SourceLocalProgram.navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> exact ⟨current,reached⟩
  | rotateRight => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork top l w => cases l with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork p u v =>
        cases Option.some.inj moved
        obtain ⟨target,located,_⟩ := context_right_valid u v w p top outside position current reached
        exact ⟨target,located⟩
  | rotateLeft => cases focus with
    | leaf => simp [SourceLocalProgram.navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [SourceLocalProgram.navigate] at moved
      | fork top v w =>
        cases Option.some.inj moved
        obtain ⟨target,located,_⟩ := context_left_valid u v w p top outside position current reached
        exact ⟨target,located⟩

theorem move_wellFormed (config : Configuration F α ρ) (valid : WellFormed config) (finger : F)
    (action : Move) (before after : Cursor α ρ) (sameTree : before.tree = config.tree)
    (moved : SourceLocalProgram.navigate action before = some after) :
    WellFormed (moveResult config finger action before after) := by
  intro other position present
  by_cases same : other = finger
  · subst other
    have equal : address after = position := by simpa only [moveResult,Function.update_self,Option.some.injEq] using present
    subst position
    exact ⟨after,locate_cursor after⟩
  · simp only [moveResult,Function.update_of_ne same] at present
    cases old : config.fingers other with
    | none => simp only [old,Option.map_none,reduceCtorEq] at present
    | some original =>
      have equal : transport action before original = position := by simpa only [old,Option.map_some,Option.some.injEq] using present
      subst position
      obtain ⟨current,reached⟩ := valid other original old
      rw [← sameTree] at reached
      exact navigate_transport action moved original current reached

theorem write_wellFormed (config : Configuration F α ρ) (valid : WellFormed config)
    (current : Cursor α ρ) (sameTree : current.tree = config.tree) (fresh : ρ) :
    WellFormed (writeResult config current fresh) := by
  intro finger position present
  obtain ⟨old,reached⟩ := valid finger position present
  apply valid_of_presence
  change (recordAt (plug (current.focus.setRoot fresh) current.ancestors) position).isSome = true
  rw [setRoot_presence]
  change (recordAt current.tree position).isSome = true
  rw [sameTree,← locate_record,reached]
  rfl

theorem Step.wellFormed {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (execution : Step source state before next after entry) (valid : WellFormed before) : WellFormed after := by
  cases execution with
  | readNone | readSome => exact valid
  | nav instruction present reached moved => exact move_wellFormed before valid _ _ _ _ (locate_tree reached) moved
  | write instruction present reached => exact write_wellFormed before valid _ (locate_tree reached) _
  | copy => exact copy_wellFormed before valid _ _

theorem Run.wellFormed {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {reads cost}
    (execution : Run source state before next after reads cost) (valid : WellFormed before) : WellFormed after := by
  induction execution with
  | halt => exact valid
  | next first rest ih => exact ih (first.wellFormed valid)

theorem Step.leaves {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (execution : Step source state before next after entry) : before.tree.shape.leaves = after.tree.shape.leaves := by
  cases execution with
  | readNone | readSome | copy => rfl
  | nav instruction present reached moved =>
    rw [← locate_tree reached]
    exact (SourceLocalProgram.navigate_sound moved).leaves
  | write instruction present reached =>
    rw [← locate_tree reached]
    exact (SourcePointer.Step.write _ _ _).leaves

theorem Run.leaves {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {reads cost}
    (execution : Run source state before next after reads cost) : before.tree.shape.leaves = after.tree.shape.leaves := by
  induction execution with
  | halt => rfl
  | next first rest ih => exact first.leaves.trans ih

end TangoSquared.Paper20261030.MultiSourceProgram
