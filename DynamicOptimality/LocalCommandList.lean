import DynamicOptimality.LocalProgramComposition

/-! Finite command sequences over the shared local-program semantics.
These are used only after a bounded observation has chosen the commands;
the interpreter has no tree-valued argument or direct subtree access. -/

namespace DynamicOptimality.LocalCommandList

open TangoSquared.MTR TangoSquared.Paper20261030.Auxiliary LocalProgram

variable {α ρ : Type*}

inductive Command (ρ : Type*) where
  | nav (action : Move)
  | write (fresh : ρ)
  | writeSize (fresh : Nat)

def program : Program (List (Command ρ)) α ρ
  | [] => .halt
  | .nav action::rest => .nav action rest
  | .write fresh::rest => .write fresh rest
  | .writeSize fresh::rest => .writeSize fresh rest

theorem run_nav {action : Move} {commands : List (Command ρ)}
    {before middle after : Metadata.Cursor α (fun _ => ρ)} {cost}
    (moved : navigate action before = some middle)
    (rest : Run program commands middle [] after [] cost) :
    Run program (.nav action::commands) before [] after [] (cost+1) := by
  apply Run.next (entry := none) (middle := commands) (current := middle)
  · exact .nav rfl moved
  · exact rest

theorem run_writeSize {fresh old : Nat} {entry : Sigma (fun _ : α => ρ)}
    {left right : RawTree (NodeRecord α (fun _ => ρ))} {outside commands after cost}
    (rest : Run program commands ⟨.node left (fresh,entry) right,outside⟩ [] after [] cost) :
    Run program (.writeSize fresh::commands) ⟨.node left (old,entry) right,outside⟩ [] after [] (cost+1) := by
  apply Run.next (entry := none) (middle := commands)
    (current := ⟨.node left (fresh,entry) right,outside⟩)
  · exact .writeSize rfl
  · exact rest

theorem run_write {fresh old : ρ} {key : α} {size : Nat}
    {left right : RawTree (NodeRecord α (fun _ => ρ))} {outside commands after cost}
    (rest : Run program commands ⟨.node left (size,⟨key,fresh⟩) right,outside⟩ [] after [] cost) :
    Run program (.write fresh::commands) ⟨.node left (size,⟨key,old⟩) right,outside⟩ [] after [] (cost+1) := by
  apply Run.next (entry := none) (middle := commands)
    (current := ⟨.node left (size,⟨key,fresh⟩) right,outside⟩)
  · exact .write rfl
  · exact rest

end DynamicOptimality.LocalCommandList
