import ChaCha.Paper20261030.SwitchedHeaderRepresentation

set_option autoImplicit false

/-! Cache correctness survives a child-payload update with unchanged wing
presence. A balanced source operation additionally refreshes the logical
root id; its endpoint and starting depth stay unchanged. -/

namespace ChaCha.Paper20261030.PrimaryHeaderController

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentCompiler LocalComponentForestCompiler

variable {α β ρ ι η : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance primaryHeaderTransportColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

theorem Represents.preserve (header : Header η) (bottom : Int) (start : Nat) (source : Source α (η × ρ))
    (old fresh : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (headerKey : α) (oldPayload freshPayload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (correct : Represents header bottom start source old headerKey oldPayload)
    (presence : ∀ q, (representation none wingOrientation headerKey freshPayload fresh q).isSome =
      (representation none wingOrientation headerKey oldPayload old q).isSome) :
    Represents header bottom start source fresh headerKey freshPayload :=
  ⟨correct.1,correct.2.1,correct.2.2.1,correct.2.2.2.1.trans (presence _).symm,correct.2.2.2.2.trans (presence _).symm⟩

theorem Represents.refresh (header : Header η) (bottom : Int) (start : Nat) (source target : Source α (η × ρ))
    (old fresh : TaggedForest (Option Bool) α (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (headerKey : α) (payload : Option Bool → α → Source β (List (Option (PhysicalDatum α ρ ι η (Option Bool)))))
    (correct : Represents header bottom start source old headerKey payload)
    (presence : ∀ q, (representation none wingOrientation headerKey payload fresh q).isSome =
      (representation none wingOrientation headerKey payload old q).isSome) :
    Represents {header with rootId := target.rootRecord.1} bottom start target fresh headerKey payload :=
  ⟨correct.1,correct.2.1,rfl,correct.2.2.2.1.trans (presence _).symm,correct.2.2.2.2.trans (presence _).symm⟩

end ChaCha.Paper20261030.PrimaryHeaderController
