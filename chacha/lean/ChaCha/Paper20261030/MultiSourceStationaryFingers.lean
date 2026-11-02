import ChaCha.Paper20261030.MultiSourceSingleCursor

/-! When a single-cursor controller only moves along edges and edits
records, every other physical finger remains at exactly the same address.
This strengthens the general compiler for short header-maintenance tours.
-/

namespace ChaCha.Paper20261030.MultiSourceSingleCursor

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ F σ : Type*} [DecidableEq F]

def EdgeMove : Move → Prop
  | .left | .right | .up => True
  | .rotateLeft | .rotateRight => False

def EdgeOnly (source : SourceLocalProgram.Program σ ρ) : Prop :=
  ∀ state move next, source state = .nav move next → EdgeMove move

theorem transport_edge (move : Move) (current : Cursor α ρ) (edge : EdgeMove move) :
    transport move current = id := by
  cases move <;> first | rfl | exact False.elim edge

theorem compile_edge_step (source : SourceLocalProgram.Program σ ρ) (edgeOnly : EdgeOnly source) (finger : F)
    {state next : σ} {before after : Cursor α ρ} {entry : Option ρ}
    (step : SourceLocalProgram.Step source state before next after entry)
    (config : Configuration F α ρ) (represented : Represents finger before config) :
    ∃ target, Step (program source finger) (some state) config (some next) target
      (entry.map (fun record => (finger,record))) ∧ Represents finger after target ∧
      ∀ other, other ≠ finger → target.fingers other = config.fingers other := by
  have reached : locate config.tree (address before) = some before := by
    rw [represented.1]; exact locate_cursor before
  cases step with
  | @read reader current instruction =>
    refine ⟨config,?_,represented,fun _ _ => rfl⟩
    exact Step.readSome (program := program source finger) (state := some state)
      (next := fun observed => observed.map (fun entry => reader entry.1 entry.2))
      (by simp only [program,instruction]) represented.2 reached
  | nav instruction moved =>
    rename_i action
    refine ⟨_,Step.nav (by simp only [program,instruction]) represented.2 reached moved,⟨rfl,?_⟩,?_⟩
    · simp only [moveResult,Function.update_self]
    · intro other different
      simp only [moveResult,Function.update_of_ne different,
        transport_edge action before (edgeOnly _ _ _ instruction),Option.map_id,id_eq]
  | @write state next fresh instruction =>
    exact ⟨_,Step.write (fresh := fresh) (by simp only [program,instruction]) represented.2 reached,
      ⟨rfl,represented.2⟩,fun _ _ => rfl⟩

theorem compile_edge_run (source : SourceLocalProgram.Program σ ρ) (edgeOnly : EdgeOnly source) (finger : F)
    {state last : σ} {before after : Cursor α ρ} {reads : List ρ} {cost : Nat}
    (run : SourceLocalProgram.Run source state before last after reads cost)
    (config : Configuration F α ρ) (represented : Represents finger before config) :
    ∃ target, Run (program source finger) (some state) config (some last) target
      (reads.map (fun record => (finger,record))) cost ∧ Represents finger after target ∧
      ∀ other, other ≠ finger → target.fingers other = config.fingers other := by
  induction run generalizing config with
  | halt stopped => exact ⟨config,.halt (by simp only [program,stopped]),represented,fun _ _ => rfl⟩
  | next first rest ih =>
    obtain ⟨middle,step,middleRep,firstFixed⟩ := compile_edge_step source edgeOnly finger first config represented
    obtain ⟨target,body,targetRep,lastFixed⟩ := ih middle middleRep
    refine ⟨target,?_,targetRep,fun other different => (lastFixed other different).trans (firstFixed other different)⟩
    simpa only [List.map_append,Option.toList_map] using Run.next step body

end ChaCha.Paper20261030.MultiSourceSingleCursor
