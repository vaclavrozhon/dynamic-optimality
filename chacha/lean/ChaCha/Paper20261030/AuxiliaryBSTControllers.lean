import ChaCha.Paper20261030.AuxiliarySourceControllers
import ChaCha.Paper20261030.GapBSTCompilerSpace

/-! End-to-end compilation of local auxiliary programs to the ordinary
decorated BST. The marked-port compiler and the appendix's gap-key
compiler compose with a uniform factor of forty-nine. The actual local
program preserves the input controller's final state and the complete
encoded payload tree. These are maintenance operations, not a complete
Tango request controller or a request-serving theorem. -/

namespace ChaCha.Paper20261030.Auxiliary.SourceController

open MTR ColoredStorage DynamicOptimality GapSource.Controller

variable {α κ ρ σ : Type*}

theorem compile_ordinary {source : LocalProgram.Program σ κ ρ} {state last : σ}
    {before after : RawTree (Record κ ρ)} {observations budget}
    (run : LocalProgram.Run source state (.atRoot before) last (.atRoot after) observations budget)
    (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat)
    (marked : ∀ i, base ≤ i → i ≤ base+before.size → boundary (ports i).rootRecord = true)
    (outside : List (SourcePointer.Frame α (MarkedRecord κ ρ))) :
    let beforeSource : SourcePointer.Cursor α (MarkedRecord κ ρ) :=
      ⟨GapSource.encode (Relabel.tree mark before) ports base,outside⟩
    let afterSource : SourcePointer.Cursor α (MarkedRecord κ ρ) :=
      ⟨GapSource.encode (Relabel.tree mark after) ports base,outside⟩
    ∃ reads cost, LocalProgram.Run (GapBST.Controller.code (code source))
      (.ready (.ready state) (GapBST.Storage.flag beforeSource)) (GapBST.Storage.cursor beforeSource)
      (.ready (.ready last) (GapBST.Storage.flag afterSource)) (GapBST.Storage.cursor afterSource)
      reads cost ∧ cost ≤ 49*budget := by
  obtain ⟨sourceReads,sourceCost,sourceRun,sourceBound⟩ := compile_root_run run ports base marked
  obtain ⟨reads,cost,compiled,bound⟩ := GapBST.Controller.compile_run (sourceRun.extend outside)
  exact ⟨reads,cost,compiled,by omega⟩

end ChaCha.Paper20261030.Auxiliary.SourceController
