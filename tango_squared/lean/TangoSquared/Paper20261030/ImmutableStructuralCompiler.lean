import TangoSquared.Paper20261030.ImmutableSourceProgram
import TangoSquared.Paper20261030.LocalStructuralCompiler

/-! Full execution with immutable identifiers and maintained structural
metadata. Initial identifiers need only be distinct. Their uniqueness at
every later instruction boundary is proved from the actual program; no
application-specific write-stability hypothesis remains. Every original
instruction costs at most thirty-eight compiled instructions.
-/

namespace TangoSquared.Paper20261030.ImmutableStructural

open ColoredStorage SourcePointer SourceLocalProgram Structural

variable {α ρ ι C σ : Type*} [DecidableEq C] [DecidableEq ι]

abbrev State (σ ρ ι C : Type*) := Compiler.State (ImmutableSource.State σ ρ ι) (ι × ρ) ι C

def ready (state : σ) : State σ ρ ι C := .ready (.ready state)

def program (source : Program σ ρ) : Program (State σ ρ ι C) ((ι × ρ) × Fields ι C) :=
  Compiler.program Prod.fst (ImmutableSource.program source)

omit [DecidableEq C] [DecidableEq ι] in
theorem unique_from (source : Program σ ρ) (initial : σ) (decorated : Cursor α (ι × ρ))
    (unique : (decorated.tree.inventory Prod.fst).Nodup) :
    Compiler.UniqueFrom Prod.fst (ImmutableSource.program source) (.ready initial) decorated := by
  intro state current reads cost steps
  have invariant := (ImmutableSource.steps_invariant steps trivial).2
  rw [← invariant]
  exact unique

theorem compile_run (source : Program σ ρ) (color : α → C)
    {initial last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run source initial before last after reads cost)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (unique : (decorated.tree.inventory Prod.fst).Nodup) :
    ∃ target actualReads actualCost,
      Run (program source) (ready initial) (cursor Prod.fst color decorated)
        (ready last) (cursor Prod.fst color target) actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧
      target.tree.inventory Prod.fst = decorated.tree.inventory Prod.fst ∧ actualCost ≤ 38*cost := by
  obtain ⟨target,taggedReads,taggedCost,taggedRun,targetErases,taggedBound⟩ :=
    ImmutableSource.compile_run source run decorated erases
  obtain ⟨actualReads,actualCost,actualRun,actualBound⟩ := Compiler.compile_run Prod.fst color taggedRun
    (unique_from source initial decorated unique)
  exact ⟨target,actualReads,actualCost,actualRun,targetErases,
    (ImmutableSource.run_invariant taggedRun trivial).2.symm,by omega⟩

theorem compile_leaf_read (source : Program σ ρ) (color : α → C)
    {initial : σ} {before : Cursor α ρ} {key : α}
    (reaches : ReachesLeafRead source initial before key)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (unique : (decorated.tree.inventory Prod.fst).Nodup) :
    ReachesLeafRead (program source) (ready initial) (cursor Prod.fst color decorated) key :=
  Compiler.compile_leaf_read Prod.fst color (ImmutableSource.compile_leaf_read source reaches decorated erases)
    (unique_from source initial decorated unique)

/-- An initial semantic assignment, not an uncharged runtime traversal.
The local initialization of these fields is a separate obligation. -/
def tag (identify : ρ → ι) (source : Source α ρ) : Source α (ι × ρ) :=
  source.mapRecords (fun record => (identify record,record))

omit [DecidableEq C] [DecidableEq ι] in
theorem tag_erases (identify : ρ → ι) (source : Source α ρ) :
    (tag identify source).mapRecords Prod.snd = source := by
  induction source <;> simp_all [tag,Source.mapRecords]

omit [DecidableEq C] [DecidableEq ι] in
theorem tag_inventory (identify : ρ → ι) (source : Source α ρ) :
    (tag identify source).inventory Prod.fst = source.inventory identify :=
  mapRecords_inventory _ _ source

theorem compile_root_run_on (source : Program σ ρ) (color : α → C)
    {initial last : σ} {before after : Source α ρ} {reads cost}
    (run : Run source initial ⟨before,[]⟩ last ⟨after,[]⟩ reads cost)
    (decorated : Source α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (unique : (decorated.inventory Prod.fst).Nodup) :
    ∃ target actualReads actualCost,
      Run (program source) (ready initial) ⟨annotate Prod.fst color none decorated,[]⟩
        (ready last) ⟨annotate Prod.fst color none target,[]⟩ actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧
      target.inventory Prod.fst = decorated.inventory Prod.fst ∧ actualCost ≤ 38*cost := by
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor α ρ) = ⟨before,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  obtain ⟨target,actualReads,actualCost,actualRun,targetErases,inventory,bounded⟩ :=
    compile_run source color run ⟨decorated,[]⟩ cursorErases unique
  have atRoot : target.ancestors = [] := by
    have equal := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using equal
  refine ⟨target.focus,actualReads,actualCost,?_,congrArg Cursor.focus targetErases,?_,bounded⟩
  · simpa only [cursor,atRoot,frames,parentId] using actualRun
  · simpa only [Cursor.tree,plug,atRoot] using inventory

theorem compile_root_leaf_read_on (source : Program σ ρ) (color : α → C)
    {initial : σ} {before : Source α ρ} {key : α}
    (reaches : ReachesLeafRead source initial ⟨before,[]⟩ key)
    (decorated : Source α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before)
    (unique : (decorated.inventory Prod.fst).Nodup) :
    ReachesLeafRead (program source) (ready initial) ⟨annotate Prod.fst color none decorated,[]⟩ key := by
  have cursorErases : (Cursor.mapRecords Prod.snd ⟨decorated,[]⟩ : Cursor α ρ) = ⟨before,[]⟩ := by
    simp only [Cursor.mapRecords,erases,List.map_nil]
  exact compile_leaf_read source color reaches ⟨decorated,[]⟩ cursorErases unique

theorem compile_root_run (source : Program σ ρ) (color : α → C) (identify : ρ → ι)
    {initial last : σ} {before after : Source α ρ} {reads cost}
    (run : Run source initial ⟨before,[]⟩ last ⟨after,[]⟩ reads cost)
    (unique : (before.inventory identify).Nodup) :
    ∃ target actualReads actualCost,
      Run (program source) (ready initial) ⟨annotate Prod.fst color none (tag identify before),[]⟩
        (ready last) ⟨annotate Prod.fst color none target,[]⟩ actualReads actualCost ∧
      target.mapRecords Prod.snd = after ∧
      target.inventory Prod.fst = before.inventory identify ∧ actualCost ≤ 38*cost := by
  have erases : (Cursor.mapRecords Prod.snd ⟨tag identify before,[]⟩ : Cursor α ρ) = ⟨before,[]⟩ := by
    simp only [Cursor.mapRecords,tag_erases,List.map_nil]
  have taggedUnique : ((Cursor.tree ⟨tag identify before,[]⟩).inventory Prod.fst).Nodup := by
    simpa only [Cursor.tree,plug,tag_inventory] using unique
  obtain ⟨target,actualReads,actualCost,actualRun,targetErases,inventory,bounded⟩ :=
    compile_run source color run ⟨tag identify before,[]⟩ erases taggedUnique
  have atRoot : target.ancestors = [] := by
    have equal := congrArg Cursor.ancestors targetErases
    simpa only [Cursor.mapRecords,List.map_eq_nil_iff] using equal
  have equalFocus : target.focus.mapRecords Prod.snd = after := congrArg Cursor.focus targetErases
  refine ⟨target.focus,actualReads,actualCost,?_,equalFocus,?_,bounded⟩
  · simpa only [cursor,atRoot,frames,parentId] using actualRun
  · simpa only [Cursor.tree,plug,atRoot,tag_inventory] using inventory

theorem compile_root_leaf_read (source : Program σ ρ) (color : α → C) (identify : ρ → ι)
    {initial : σ} {before : Source α ρ} {key : α}
    (reaches : ReachesLeafRead source initial ⟨before,[]⟩ key)
    (unique : (before.inventory identify).Nodup) :
    ReachesLeafRead (program source) (ready initial) ⟨annotate Prod.fst color none (tag identify before),[]⟩ key := by
  have erases : (Cursor.mapRecords Prod.snd ⟨tag identify before,[]⟩ : Cursor α ρ) = ⟨before,[]⟩ := by
    simp only [Cursor.mapRecords,tag_erases,List.map_nil]
  exact compile_leaf_read source color reaches ⟨tag identify before,[]⟩ erases
    (by simpa only [Cursor.tree,plug,tag_inventory] using unique)

end TangoSquared.Paper20261030.ImmutableStructural
