import ChaCha.Paper20261030.LocalComponentOriginalAccess
import ChaCha.Paper20261030.MultiSourceMask

/-! The physical virtual-header piece stays at its own root even when
the stored logical cursor is below the source root. Masked register
representations also imply the same actual reached payload positions.
-/

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler

variable {α β ρ ι η C : Type*} [DecidableEq α] [LinearOrder C]

theorem virtual_present_root (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι) :
    ∃ header, representation virtualColor orientation headerKey payload forest virtualColor = some ⟨header,[]⟩ := by
  simp only [representation,PayloadForestController.transform,VirtualHeaderController.encode,ite_true,Option.map_some]
  exact ⟨_,rfl⟩

end ChaCha.Paper20261030.LocalComponentCompiler

namespace ChaCha.Paper20261030.SecondaryDecomposition.OriginalAccessController

open ColoredStorage SourcePointer ComponentEndpointController LocalComponentForestCompiler

variable {β ι η C : Type*} [DecidableEq C]

theorem exposes_unmask (config : MultiSourceProgram.Configuration C β (Record ι η C))
    (active : C → Bool) (q : C) (payload : Source β (List (Option (Datum ι η C))))
    (exposed : Exposes (config.mask active) q payload) : Exposes config q payload := by
  obtain ⟨position,current,routing,present,reached,focus⟩ := exposed
  exact ⟨position,current,routing,(MultiSourceProgram.mask_present active config q position present).2,reached,focus⟩

end ChaCha.Paper20261030.SecondaryDecomposition.OriginalAccessController
