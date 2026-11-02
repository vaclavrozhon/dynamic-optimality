import ChaCha.Paper20261030.PrimaryHeaderFromRecord
import ChaCha.Paper20261030.ComponentOriginalKeys

set_option autoImplicit false

/-! The installed switched headers describe the represented components:
their inherited endpoints and starts, current logical root ids, and exact
presence of the two real wings. -/

namespace ChaCha.Paper20261030.PrimaryHeaderController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentCompiler LocalComponentForestCompiler

variable {α β ρ ι η : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance switchedHeaderRepresentationColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def Represents (header : Header η) (bottom : Int) (start : Nat) (source : Source α (η × ρ))
    (forest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (headerKey : α) (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool))))) : Prop :=
  header.bottom = bottom ∧ header.start = start ∧ header.rootId = source.rootRecord.1 ∧
    header.leftWing = (representation none wingOrientation headerKey payload forest (some true)).isSome ∧
    header.rightWing = (representation none wingOrientation headerKey payload forest (some false)).isSome

theorem switched_represents (old incoming : Header η) (records : HeadBoundary.Records (η × ρ) η (Option Bool))
    (activeSource dormantSource : Source α (η × ρ)) (activeColor dormantColor : α → Option Bool)
    (activeForest dormantForest : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (activeRep : ProjectionForest.Represents activeColor ⟨annotate Prod.fst activeColor none activeSource,[]⟩ (erase activeForest))
    (dormantRep : ProjectionForest.Represents dormantColor ⟨annotate Prod.fst dormantColor none dormantSource,[]⟩ (erase dormantForest))
    (activeRoot : records.low = (annotate Prod.fst activeColor none activeSource).rootRecord)
    (dormantRoot : records.oldHigh = (annotate Prod.fst dormantColor none dormantSource).rootRecord)
    (headerKey : α)
    (activePayload dormantPayload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool))))) :
    Represents (switched old incoming records).1 incoming.bottom old.start activeSource activeForest headerKey activePayload ∧
      Represents (switched old incoming records).2 old.bottom incoming.start dormantSource dormantForest headerKey dormantPayload := by
  simp only [switched,activeRoot,dormantRoot]
  exact ⟨fromRoot_correct incoming.bottom old.start activeSource activeColor activeForest activeRep wingOrientation headerKey activePayload,
    fromRoot_correct old.bottom incoming.start dormantSource dormantColor dormantForest dormantRep wingOrientation headerKey dormantPayload⟩

end ChaCha.Paper20261030.PrimaryHeaderController
