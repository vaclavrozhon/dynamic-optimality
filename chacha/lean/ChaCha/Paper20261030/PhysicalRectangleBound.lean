import ChaCha.Paper20261030.MaintainedPhysicalRun
import ChaCha.Paper20261030.AbstractBound

/-!
# The geometric bound for complete physical request traces

This is the actual original-key leaf-oriented source-pointer trace bound,
from a represented initial state. It includes the whole primary loop,
completion resets, and actual visits to the requested original keys.
Charged initialization, the bounded local controller, and compilation to
the ordinary BST model remain separate obligations.
-/

namespace ChaCha.Paper20261030.Dyadic

open Rectangles Secondary SecondaryDecomposition LocalReferences SourcePointer

theorem physical_run_rectangle_bound {h : Nat} (reference : DepthTree 0 h)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key)
    (components : Components Int)
    (valid : Components.Valid (completedDepth reference) (canonical (h+1) 0) (canonical_perfect (h+1) 0)
      (fun _ => true) components) :
    ∃ (finalPerfect : (completeRun (h+1) (MemoryState.initial (canonical (h+1) 0)) requests).primary.Perfect (h+1))
      (out : Components Int),
      Components.Valid (completedDepth reference)
        (completeRun (h+1) (MemoryState.initial (canonical (h+1) 0)) requests).primary finalPerfect
        (completeRun (h+1) (MemoryState.initial (canonical (h+1) 0)) requests).preference out ∧
      Services (physicalState (canonical (h+1) 0) components) requests
        (physicalState (completeRun (h+1) (MemoryState.initial (canonical (h+1) 0)) requests).primary out)
        ((requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1)) * physicalRequestFactor reference) := by
  have members : ∀ key ∈ requests, key ∈ (canonical (h+1) 0).leaves :=
    fun key member => (canonical_zero_mem (h+1) key).mpr (keys key member)
  obtain ⟨finalPerfect,out,outValid,execution⟩ := maintained_physical_run reference
    (MemoryState.initial (canonical (h+1) 0)) (canonical_perfect (h+1) 0) (canonical_nodup (h+1) 0)
    requests members components valid
  have work := abstract_work_bound_leaves reference requests keys
  simp only [abstractWork,PreferredProjection.PrefRouter.depthAccessCount_eq,secondaryCost,
    MemoryState.initial] at work
  have costBound : memoryCost (memoryKeys (canonical (h+1) 0) reference)
      (MemoryState.initial (canonical (h+1) 0)) requests + (canonical (h+1) 0).runFlips requests + requests.length ≤
      requests.length+13*rectangleBound (accessPoints requests)+6*2^(h+1) := by
    simpa only [MemoryState.initial] using (show _ ≤ _ by omega)
  exact ⟨finalPerfect,out,outValid,execution.mono (Nat.mul_le_mul_right (physicalRequestFactor reference) costBound)⟩

end ChaCha.Paper20261030.Dyadic
