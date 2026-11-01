import TangoSquared.Paper20261030.LocalPackedWrite
import TangoSquared.Paper20261030.PhysicalForestCompiler

/-! Packed logical writes with maintained physical pointer metadata.
The source identifier is immutable; application and structural fields
may change. Both physical and logical identifier uniqueness survive.
-/

namespace TangoSquared.Paper20261030.PhysicalPackedWriteController

open ColoredStorage SourcePointer ForestLocalProgram PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C] [Fintype C]

abbrev State (ρ ι C : Type*) := PhysicalForestCompiler.State (PackedWriteController.State C ρ) C ρ ι

def program (identifier : ρ → η) (wanted : η) (fresh : ρ) : Program (State ρ ι C) C (Record ρ ι) :=
  PhysicalForestCompiler.program (PackedWriteController.program identifier wanted fresh)

theorem write [DecidableEq α] (identifier : ρ → η) (color : α → C) (source : Cursor α ρ)
    (fresh : ρ) (sameId : identifier fresh = identifier source.focus.rootRecord)
    (forest : TaggedForest C α ρ ι) (represented : ProjectionForest.Represents color source (erase forest))
    (physicalUnique : Unique forest) (logicalUnique : (source.tree.inventory identifier).Nodup) :
    ∃ target reads cost,
      Run (program identifier (identifier source.focus.rootRecord) fresh)
        (.ready (.scan (Finset.univ.sort (· ≤ ·)))) (encode forest) (.ready .done) (encode target) reads cost ∧
      ProjectionForest.Represents color ⟨source.focus.setRoot fresh,source.ancestors⟩ (erase target) ∧
      Unique target ∧ ((Cursor.tree ⟨source.focus.setRoot fresh,source.ancestors⟩).inventory identifier).Nodup ∧
      cost ≤ 38*(Fintype.card C+1) := by
  obtain ⟨bare,readWord,sourceCost,sourceRun,bareRep,bounded⟩ :=
    PackedWriteController.write identifier color source fresh (erase forest) represented logicalUnique
  obtain ⟨target,reads,cost,actual,targetErases,targetUnique,actualBound⟩ :=
    PhysicalForestCompiler.compile_run _ sourceRun forest rfl physicalUnique
  have inventory := plug_inventory_congr identifier (Source.inventory_setRoot identifier source.focus fresh sameId) source.ancestors
  refine ⟨target,reads,cost,actual,?_,targetUnique,?_,by omega⟩
  · rw [targetErases]; exact bareRep
  · change ((plug (source.focus.setRoot fresh) source.ancestors).inventory identifier).Nodup
    rw [inventory]
    exact logicalUnique

end TangoSquared.Paper20261030.PhysicalPackedWriteController
