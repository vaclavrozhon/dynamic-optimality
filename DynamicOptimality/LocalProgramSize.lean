import DynamicOptimality.LocalProgramComposition

/-! Tree size and cursor depth invariants for local programs. These facts
concern the existing physical BST: a local record write changes no node,
and the cursor's ancestor frames are actual vertices of that same tree. -/

namespace DynamicOptimality.LocalProgram

open TangoSquared.MTR
open TangoSquared.Paper20261030.Auxiliary

variable {κ α ρ σ : Type*}

theorem plug_size_congr {a b : RawTree κ} (same : a.size = b.size) (rest : List (Pointer.Frame κ)) :
    (Pointer.plug a rest).size = (Pointer.plug b rest).size := by
  induction rest generalizing a b with
  | nil => exact same
  | cons first rest ih =>
    cases first <;> apply ih <;> simp only [Tree.size,same]

theorem pointer_step_size {before after : Pointer.Cursor κ} (step : Pointer.Step before after) :
    before.tree.size = after.tree.size := by
  cases step with
  | left | right | upLeft | upRight => rfl
  | rotateRight => apply plug_size_congr; simp only [Tree.size]; omega
  | rotateLeft => apply plug_size_congr; simp only [Tree.size]; omega

theorem metadata_step_size {before after : Metadata.Cursor α (fun _ => ρ)} (step : Metadata.Step before after) :
    before.tree.size = after.tree.size := by
  cases step with
  | nav move => exact pointer_step_size move
  | write | writeValue => apply plug_size_congr; rfl

theorem metadata_trace_size {before after : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (run : Metadata.Trace before reads after cost) : before.tree.size = after.tree.size := by
  induction run with
  | nil => rfl
  | step move rest ih => exact (metadata_step_size move).trans ih
  | read observed rest ih => exact ih

theorem Step.tree_size {program : Program σ α ρ} {state next : σ}
    {before after : Metadata.Cursor α (fun _ => ρ)} {entry}
    (step : Step program state before next after entry) : before.tree.size = after.tree.size :=
  metadata_trace_size step.trace

theorem Steps.tree_size {program : Program σ α ρ} {state last : σ}
    {before after : Metadata.Cursor α (fun _ => ρ)} {reads cost}
    (run : Steps program state before last after reads cost) : before.tree.size = after.tree.size := by
  induction run with
  | nil => rfl
  | next first rest ih => exact first.tree_size.trans ih

theorem cursor_depth_bound (cursor : Pointer.Cursor κ) :
    cursor.focus.size+cursor.ancestors.length ≤ cursor.tree.size := by
  rcases cursor with ⟨focus,rest⟩
  induction rest generalizing focus with
  | nil => simp [Pointer.Cursor.tree,Pointer.plug]
  | cons first rest ih =>
    cases first with
    | left key right =>
      have bound := ih (.node focus key right)
      simp only [Pointer.Cursor.tree,Pointer.plug,Tree.size,List.length_cons] at bound ⊢
      omega
    | right left key =>
      have bound := ih (.node left key focus)
      simp only [Pointer.Cursor.tree,Pointer.plug,Tree.size,List.length_cons] at bound ⊢
      omega

theorem navigate_depth {action : Move} {before after : Pointer.Cursor κ}
    (moved : navigate action before = some after) :
    match action with
    | .left | .right => after.ancestors.length = before.ancestors.length+1
    | .up => after.ancestors.length+1 = before.ancestors.length
    | .rotateRight | .rotateLeft => after.ancestors.length = before.ancestors.length := by
  rcases before with ⟨focus,rest⟩
  cases action with
  | left => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases left with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl
  | right => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases right with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl
  | up => cases rest with
    | nil => simp [navigate] at moved
    | cons first rest => cases first with
      | left key right => cases Option.some.inj moved; rfl
      | right left key => cases Option.some.inj moved; rfl
  | rotateRight => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases left with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl
  | rotateLeft => cases focus with
    | empty => simp [navigate] at moved
    | node left key right => cases right with
      | empty => simp [navigate] at moved
      | node a x b => cases Option.some.inj moved; rfl

end DynamicOptimality.LocalProgram
