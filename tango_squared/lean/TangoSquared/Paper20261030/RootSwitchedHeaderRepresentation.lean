import TangoSquared.Paper20261030.SwitchedHeaderRepresentation

set_option autoImplicit false

/-! The minimum-depth switch uses the incoming high record as the active
root. This adapts the existing four-record header computation to the
common observed exchange-data interface. -/

namespace TangoSquared.Paper20261030.PrimaryHeaderController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentCompiler LocalComponentForestCompiler

variable {α β ρ ι η : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def switchedMinimum (old incoming : Header η) (records : HeadBoundary.Records (η × ρ) η (Option Bool)) : Header η × Header η :=
  switchedRoot old incoming ⟨records.oldHigh,records.incomingHigh,records.oldTerminal,records.incomingTerminal⟩

theorem switched_minimum_represents (old incoming : Header η) (records : HeadBoundary.Records (η × ρ) η (Option Bool))
    (activeSource dormantSource : Source α (η × ρ)) (activeColor dormantColor : α → Option Bool)
    (activeForest dormantForest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (activeRep : ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeSource,[]⟩ (erase activeForest))
    (dormantRep : ProjectionForest.Represents dormantColor ⟨annotate Prod.fst dormantColor none dormantSource,[]⟩ (erase dormantForest))
    (activeRoot : records.incomingHigh = (annotate Prod.fst activeColor none activeSource).rootRecord)
    (dormantRoot : records.oldHigh = (annotate Prod.fst dormantColor none dormantSource).rootRecord)
    (headerKey : α)
    (activePayload dormantPayload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool))))) :
    Represents (switchedMinimum old incoming records).1 incoming.bottom old.start activeSource activeForest headerKey activePayload ∧
      Represents (switchedMinimum old incoming records).2 old.bottom incoming.start dormantSource dormantForest headerKey dormantPayload := by
  simp only [switchedMinimum,switchedRoot,activeRoot,dormantRoot]
  exact ⟨fromRoot_correct incoming.bottom old.start activeSource activeColor activeForest activeRep wingOrientation headerKey activePayload,
    fromRoot_correct old.bottom incoming.start dormantSource dormantColor dormantForest dormantRep wingOrientation headerKey dormantPayload⟩

end TangoSquared.Paper20261030.PrimaryHeaderController
