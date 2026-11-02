import ChaCha.Paper20261030.GapBSTProgramCompiler

/-! Embedding each checked gap-encoding helper into its caller. The first
paid operation changes from the caller's phase to the helper's phase;
there is no uncharged cursor movement or record access at the boundary. -/

namespace ChaCha.Paper20261030.GapBST.Controller

open ColoredStorage Storage DynamicOptimality

variable {α ρ σ : Type*}

def Navigation.move : Navigation → LocalProgram.Move
  | .left => .left
  | .right => .right
  | .up => .up

def rotationMove (right : Bool) : LocalProgram.Move := if right then .rotateRight else .rotateLeft

theorem navigation_prefix {source : SourceLocalProgram.Program σ ρ} {state next : σ} {action : Navigation}
    (instruction : source state = .nav (Navigation.move action) next) {slot output : Flag}
    {before after : Auxiliary.Metadata.Cursor α (fun _ => Slots ρ)} {reads cost}
    (run : LocalProgram.Run (navigationProgram action) (.start slot) before (.done output) after reads cost) :
    LocalProgram.Steps (code source) (.ready state slot) before (.ready next output) after reads cost := by
  have lifted := run.map_prefix (finishNavigation next action) (navigation_code source next action)
  apply lifted.change_start (run.positive (by simp [navigationProgram]))
  cases action <;> simp only [code,instruction,Navigation.move,startMove,startNavigation,finishNavigation]

theorem rotation_prefix {source : SourceLocalProgram.Program σ ρ} {state next : σ} {right : Bool}
    (instruction : source state = .nav (rotationMove right) next)
    {before after : Auxiliary.Metadata.Cursor α (fun _ => Slots ρ)} {reads cost}
    (run : LocalProgram.Run (rotationProgram right) .start before .done after reads cost) :
    LocalProgram.Steps (code source) (.ready state .internal) before (.ready next .internal) after reads cost := by
  have lifted := run.map_prefix (finishRotation next right) (rotation_code source next right)
  apply lifted.change_start (run.positive (by simp [rotationProgram]))
  cases right <;> simp only [code,instruction,rotationMove,Bool.false_eq_true,if_false,if_true,
    startMove,startRotation,finishRotation]

theorem write_prefix {source : SourceLocalProgram.Program σ ρ} {state next : σ} {fresh : ρ}
    (instruction : source state = .write fresh next) {slot : Flag}
    {before after : Auxiliary.Metadata.Cursor α (fun _ => Slots ρ)} {reads cost}
    (run : LocalProgram.Run (writeProgram fresh) (.start slot) before .done after reads cost) :
    LocalProgram.Steps (code source) (.ready state slot) before (.ready next slot) after reads cost := by
  have lifted := run.map_prefix (finishWrite next slot fresh) (write_code source next slot fresh)
  apply lifted.change_start (run.positive (by simp [writeProgram]))
  simp only [code,instruction,finishWrite]

theorem read_prefix {source : SourceLocalProgram.Program σ ρ} {state : σ} {next : ρ → Bool → σ}
    (instruction : source state = .read next) (logical : SourcePointer.Cursor α ρ) :
    ∃ reads, LocalProgram.Steps (code source) (.ready state (flag logical)) (Storage.cursor logical)
      (.ready (next logical.focus.rootRecord (SourceLocalProgram.isLeaf logical.focus)) (flag logical))
      (Storage.cursor logical) reads 1 := by
  obtain ⟨entry,atRecord,contains⟩ := cursor_record logical
  have observed : ∃ view : LocalProgram.View α (Slots ρ),
      LocalProgram.observe (Storage.cursor logical) = some view ∧ view.entry = entry := by
    cases focusEq : (Storage.cursor logical).focus with
    | empty => simp [focusEq,MTR.Tree.rootKey] at atRecord
    | node left value right =>
      have same : value = entry := by simpa only [focusEq,MTR.Tree.rootKey,Option.some.injEq] using atRecord
      exact ⟨⟨value,LocalProgram.empty left,LocalProgram.empty right⟩,by simp [LocalProgram.observe,focusEq],same⟩
  obtain ⟨view,observed,same⟩ := observed
  have got : (flag logical).get view.entry.2.2 = some logical.focus.rootRecord := by
    rw [same,flag_read]
    exact contains
  refine ⟨[view.entry],?_⟩
  apply LocalProgram.Steps.next (entry := some view.entry) (cost := 0)
  · apply LocalProgram.Step.read (view := view) (next := fun seen =>
      match (flag logical).get seen.entry.2.2 with
      | none => State.error
      | some value => State.ready (next value (leafFlag (flag logical))) (flag logical))
    · simp only [code,instruction]
      rfl
    · exact observed
  · simp only [got,flag_isLeaf]
    exact .nil _ _

end ChaCha.Paper20261030.GapBST.Controller
