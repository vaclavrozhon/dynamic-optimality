import TangoSquared.Paper20261030.ForestWriteLabels
import TangoSquared.Paper20261030.SourceForestLift
import TangoSquared.Paper20261030.CheckedImmutableStructural

set_option autoImplicit false

/-! The existing checked structural compiler proves write stability
at every instruction. Lifting its singleton records into a physical
forest therefore retains the stronger per-vertex label guarantee. -/

namespace TangoSquared.Paper20261030.SourceForestWriteLabels

open ColoredStorage SourcePointer ForestLocalProgram

variable {α ρ ι C D σ : Type*} [DecidableEq C] [LinearOrder D] [Fintype D]

theorem stable (identifier : ρ → ι) (color : α → D)
    (source : SourceLocalProgram.Program σ (ρ × Structural.Fields ι D)) (state : σ)
    (current : Cursor α (ρ × Structural.Fields ι D))
    (ready : PackedReadiness.Ready identifier color (source state) current)
    (q : C) (forest : ProjectionForest.State C α (ρ × Structural.Fields ι D))
    (atCursor : forest q = some (SourceForestLift.packet current)) :
    ForestWriteLabels.Stable (fun record => identifier record.1)
      (SourceForestLift.program q source (.running state)) forest := by
  cases code : source state with
  | halt | read | nav => simp only [SourceForestLift.program,code,ForestWriteLabels.Stable]
  | write fresh next =>
    simp only [SourceForestLift.program,code,ForestWriteLabels.Stable]
    intro actual present
    have equal := Option.some.inj (present.symm.trans atCursor)
    subst actual
    have same : identifier fresh.1 = identifier current.focus.rootRecord.1 := by
      simpa only [code,PackedReadiness.Ready] using ready
    simp only [SourceForestLift.packet,Cursor.mapRecords,Source.mapRecords_root,List.map_cons,List.map_nil,same]

theorem lift (identifier : ρ → ι) (color : α → D) (q : C)
    {source : SourceLocalProgram.Program σ (ρ × Structural.Fields ι D)} {state last : σ}
    {before after : Cursor α (ρ × Structural.Fields ι D)} {reads cost}
    (checked : PackedReadiness.CheckedRun identifier color source state before last after reads cost)
    (forest : ProjectionForest.State C α (ρ × Structural.Fields ι D))
    (atCursor : forest q = some (SourceForestLift.packet before)) :
    ForestWriteLabels.Run (fun record => identifier record.1) (SourceForestLift.program q source)
      (.running state) forest (.running last)
      (Function.update forest q (some (SourceForestLift.packet after)))
      (reads.map (fun record => (q,[record]))) cost := by
  induction checked generalizing forest with
  | halt stopped =>
    rw [← atCursor,Function.update_eq_self]
    exact .halt (by simp only [SourceForestLift.program,stopped])
  | next first ready rest ih =>
    have compiled := SourceForestLift.step q first forest atCursor
    have tail := ih (Function.update forest q _) (Function.update_self _ _ _)
    have all := ForestWriteLabels.Run.next compiled (stable identifier color source _ _ ready q forest atCursor) tail
    simpa only [Function.update_idem,List.map_append,Option.toList_map] using all

end TangoSquared.Paper20261030.SourceForestWriteLabels
