import TangoSquared.Paper20261030.CheckedStructuralContext

/-! A complete structural write with every instruction's fields checked.
-/

namespace TangoSquared.Paper20261030.Structural.WriteController

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

theorem checked_write_cursor (identifier : ρ → ι) (color : α → C)
    (source : Source α ρ) (fresh : ρ) (outside : List (Frame α ρ))
    (sameId : identifier fresh = identifier source.rootRecord)
    (unique : ((plug source outside).inventory identifier).Nodup) :
    ∃ reads cost, CheckedRun identifier color (ContextController.program identifier (program identifier fresh) .start) .start
      (cursor identifier color ⟨source,outside⟩) .done
      (cursor identifier color ⟨source.setRoot fresh,outside⟩) reads cost ∧ cost ≤ 16 := by
  obtain ⟨reads,cost,body,bounded⟩ := checked_write identifier color (parentId identifier outside)
    source fresh (frames identifier color source outside) sameId
  obtain ⟨allReads,allCost,actual,total⟩ := ContextController.checked_lift identifier color
    (program identifier fresh) .start .done source (source.setRoot fresh) outside
    (by cases source <;> rfl) unique body rfl
  exact ⟨allReads,allCost,actual,by omega⟩

end TangoSquared.Paper20261030.Structural.WriteController
