import ChaCha.Paper20261030.MultiSourcePairSteps

set_option autoImplicit false

/-!
# Executing a multifinger component below an unchanged outer context

Every local finger receives the same outer address prefix. The context
and addresses appear only in the proof semantics; the running program
is unchanged. Each local instruction remains one actual instruction,
and all reads return the same record. Additional external registers can
be supplied separately by the register-extension compiler.
-/

namespace ChaCha.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer

variable {α ρ F σ : Type*} [DecidableEq F]

def Configuration.empty (tree : Source α ρ) : Configuration F α ρ := ⟨tree,fun _ => none⟩

theorem Run.join_left {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (execution : Run source state before last after reads cost) (record : ρ) (sibling : Source α ρ) :
    Run source state (join record before (.empty sibling)) last (join record after (.empty sibling)) reads cost := by
  induction execution with
  | halt stopped => exact .halt stopped
  | next first rest ih => exact .next (first.join_left record (.empty sibling) (fun _ _ => rfl)) ih

theorem Run.join_right {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (execution : Run source state before last after reads cost) (record : ρ) (sibling : Source α ρ) :
    Run source state (join record (.empty sibling) before) last (join record (.empty sibling) after) reads cost := by
  induction execution with
  | halt stopped => exact .halt stopped
  | next first rest ih => exact .next (first.join_right record (.empty sibling) (fun _ _ => rfl)) ih

def Configuration.extend (config : Configuration F α ρ) : List (Frame α ρ) → Configuration F α ρ
  | [] => config
  | .left record sibling::rest => (join record config (.empty sibling)).extend rest
  | .right sibling record::rest => (join record (.empty sibling) config).extend rest

theorem Configuration.extend_tree (config : Configuration F α ρ) (outside : List (Frame α ρ)) :
    (config.extend outside).tree = plug config.tree outside := by
  induction outside generalizing config with
  | nil => rfl
  | cons frame rest ih => cases frame <;> exact ih _

theorem Configuration.extend_finger (config : Configuration F α ρ) (outside : List (Frame α ρ)) (finger : F) :
    (config.extend outside).fingers finger =
      (config.fingers finger).map (fun position => outside.reverse.map SourcePositions.direction ++ position) := by
  induction outside generalizing config with
  | nil => simp only [extend,List.reverse_nil,List.map_nil,List.nil_append,Option.map_id']
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      rw [extend,ih]
      cases present : config.fingers finger <;>
        simp only [join,Configuration.empty,present,Option.map_none,Option.map_some,List.reverse_cons,List.map_append,
          List.map_cons,List.map_nil,SourcePositions.direction,List.append_assoc,List.singleton_append]
    | right sibling record =>
      rw [extend,ih]
      cases present : config.fingers finger <;>
        simp only [join,Configuration.empty,present,Option.map_none,Option.map_some,List.reverse_cons,List.map_append,
          List.map_cons,List.map_nil,SourcePositions.direction,List.append_assoc,List.singleton_append]

theorem Configuration.extend_wellFormed (config : Configuration F α ρ) (outside : List (Frame α ρ))
    (valid : WellFormed config) : WellFormed (config.extend outside) := by
  induction outside generalizing config with
  | nil => exact valid
  | cons frame rest ih => cases frame with
    | left record sibling =>
      exact ih _ (join_wellFormed record config (.empty sibling) valid (by intro _ _ present; cases present))
    | right sibling record =>
      exact ih _ (join_wellFormed record (.empty sibling) config (by intro _ _ present; cases present) valid)

theorem Run.extend {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (execution : Run source state before last after reads cost) (outside : List (Frame α ρ)) :
    Run source state (before.extend outside) last (after.extend outside) reads cost := by
  induction outside generalizing before after with
  | nil => exact execution
  | cons frame rest ih => cases frame with
    | left record sibling => exact ih (execution.join_left record sibling)
    | right sibling record => exact ih (execution.join_right record sibling)

end ChaCha.Paper20261030.MultiSourceProgram
