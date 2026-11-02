import ChaCha.Paper20261030.LocalComponentCompiler
import ChaCha.Paper20261030.ForestConnectorPositions
import ChaCha.Paper20261030.MultiSourceService

/-! Physical completion at a component's bottom original key. The
compiler leaves the header finger on that leaf. A final ordinary record
read supplies actual leaf service, with one extra charged instruction.
The primary loop uses this when its request equals the component bottom.
-/

namespace ChaCha.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler

variable {α β ρ ι η C σ : Type*} [DecidableEq α] [LinearOrder C]

theorem header_leaf (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (key : β) (extra : List (Option (PhysicalDatum α ρ ι η C)))
    (payloadLeaf : payload virtualColor headerKey = .leaf key extra) :
    ∃ records, representation virtualColor orientation headerKey payload forest virtualColor =
      some ⟨.leaf key records,[]⟩ := by
  simp [representation,PayloadForestController.transform,VirtualHeaderController.encode,
    SourcePayloads.cursor,SourcePayloads.graft,payloadLeaf,Source.rootRecord,Source.setRoot]

theorem serve_run (source : MultiSourceProgram.Program σ C (List (Option (PhysicalDatum α ρ ι η C))))
    {initial last : σ} {before after : MultiSourceProgram.Configuration C β (List (Option (PhysicalDatum α ρ ι η C)))}
    {reads cost} (run : MultiSourceProgram.Run source initial before last after reads cost)
    (virtualColor : C) (orientation : C → Bool) (headerKey : α)
    (payload : C → α → Source β (List (Option (PhysicalDatum α ρ ι η C))))
    (forest : TaggedForest C α (LocalColoredCompiler.LogicalRecord ρ η C) ι)
    (layout : Source C Unit) (virtualMember : virtualColor ∈ ForestConnector.colors layout)
    (assembled : ForestConnector.assemble (representation virtualColor orientation headerKey payload forest) layout = some after)
    (key : β) (extra : List (Option (PhysicalDatum α ρ ι η C)))
    (payloadLeaf : payload virtualColor headerKey = .leaf key extra) :
    ∃ records, MultiSourceProgram.Serves (ReadCompletionController.program source virtualColor) key
      (some initial) before none after (reads++[(virtualColor,records)]) (cost+1) := by
  obtain ⟨records,present⟩ := header_leaf virtualColor orientation headerKey payload forest key extra payloadLeaf
  obtain ⟨position,outside,finger,reached⟩ := ForestConnector.assemble_cursor _ layout after assembled
    virtualColor virtualMember ⟨.leaf key records,[]⟩ present
  exact ⟨records,ReadCompletionController.serve source virtualColor run key records position outside finger reached⟩

end ChaCha.Paper20261030.LocalComponentCompiler
