import TangoSquared.Paper20261030.MultiSourceRecordMap

set_option autoImplicit false

/-! Changing only the representation of vertex records. A bijection is
applied to writes and inverted on reads; no extra operation is needed.
This lets the existing metadata compiler use the immutable-id-first
record convention of the physical head controller. -/

namespace TangoSquared.Paper20261030.MultiSourceRecordEquivalence

open ColoredStorage SourcePointer MultiSourceProgram

variable {α ρ τ υ F σ : Type*} [DecidableEq F]

def instruction (encode : ρ ≃ τ) : Instruction σ F ρ → Instruction σ F τ
  | .halt => .halt
  | .read finger next => .read finger (fun observed => next
      (observed.map (fun (pair : τ × Bool) => (encode.symm pair.1,pair.2))))
  | .nav finger action next => .nav finger action next
  | .write finger fresh next => .write finger (encode fresh) next
  | .copy destination origin next => .copy destination origin next

def program (encode : ρ ≃ τ) (source : Program σ F ρ) : Program σ F τ :=
  fun state => instruction encode (source state)

def observation (encode : ρ ≃ τ) (entry : F × ρ) : F × τ := (entry.1,encode entry.2)

theorem map_source_comp (first : ρ → τ) (second : τ → υ) (tree : Source α ρ) :
    (tree.mapRecords first).mapRecords second = tree.mapRecords (second ∘ first) := by
  induction tree <;> simp_all only [Source.mapRecords,Function.comp_apply]

theorem map_comp (first : ρ → τ) (second : τ → υ) (config : Configuration F α ρ) :
    (config.mapRecords first).mapRecords second = config.mapRecords (second ∘ first) := by
  exact congrArg (fun tree => Configuration.mk tree config.fingers) (map_source_comp first second config.tree)

theorem map_source_id (tree : Source α ρ) : tree.mapRecords id = tree := by
  induction tree <;> simp_all only [Source.mapRecords,id_eq]

theorem map_id (config : Configuration F α ρ) : config.mapRecords id = config := by
  cases config
  exact congrArg (fun tree => Configuration.mk tree _) (map_source_id _)

theorem compile_step (encode : ρ ≃ τ) {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry : Option (F × ρ)}
    (step : Step source state before next after entry) :
    Step (program encode source) state (before.mapRecords encode) next (after.mapRecords encode)
      (entry.map (observation encode)) := by
  cases step with
  | @readNone finger next code absent =>
    exact Step.readNone (program := program encode source) (state := state) (config := before.mapRecords encode) (finger := finger)
      (next := fun (observed : View τ) => next (observed.map (fun (pair : τ × Bool) => (encode.symm pair.1,pair.2))))
      (congrArg (instruction encode) code) absent
  | @readSome finger position current next code present reached =>
    have actual := Step.readSome (program := program encode source) (state := state)
      (config := before.mapRecords encode) (current := current.mapRecords encode)
      (congrArg (instruction encode) code) present
      (by simp only [Configuration.mapRecords,SourcePositions.locate_mapRecords,reached,Option.map_some])
    simpa only [Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords,Option.map_some,
      Equiv.symm_apply_apply,observation] using actual
  | nav code present reached moved =>
    rw [moveResult_mapRecords]
    exact .nav (congrArg (instruction encode) code) present
      (by simp only [Configuration.mapRecords,SourcePositions.locate_mapRecords,reached,Option.map_some])
      (by rw [← navigate_mapRecords,moved]; rfl)
  | write code present reached =>
    rw [writeResult_mapRecords]
    exact .write (congrArg (instruction encode) code) present
      (by simp only [Configuration.mapRecords,SourcePositions.locate_mapRecords,reached,Option.map_some])
  | copy code => exact .copy (congrArg (instruction encode) code)

theorem compile_run (encode : ρ ≃ τ) {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost) :
    Run (program encode source) state (before.mapRecords encode) last (after.mapRecords encode)
      (reads.map (observation encode)) cost := by
  induction run with
  | halt stopped => exact .halt (congrArg (instruction encode) stopped)
  | next first rest ih =>
    simpa only [List.map_append,Option.toList_map] using Run.next (compile_step encode first) ih

end TangoSquared.Paper20261030.MultiSourceRecordEquivalence
