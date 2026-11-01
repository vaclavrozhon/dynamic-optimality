import TangoSquared.Paper20261030.GapBSTMetadataAccess
import TangoSquared.Paper20261030.SharedOPTBound

/-! The maintained Tango-squared histories in the actual ordinary BST
metadata layout. Every request is served at an original key. The complete
endpoint state has at most fifteen bounded datums per physical vertex.
Local synthesis of the source controller and initialization is separate. -/

namespace TangoSquared.Paper20261030.SecondaryDecomposition

open ColoredStorage SourcePointer PreferredProjection Secondary LocalReferences

variable {α : Type*} [DecidableEq α]

theorem maintained_metadata_run {h : Nat} (reference : DepthTree 0 h)
    (initial : MemoryState α) (perfect : initial.primary.Perfect (h+1)) (distinct : initial.primary.leaves.Nodup)
    (requests : List α) (members : ∀ key ∈ requests, key ∈ initial.primary.leaves)
    (components : Components α)
    (valid : Components.Valid (completedDepth reference) initial.primary perfect initial.preference components) :
    ∃ (finalPerfect : (completeRun (h+1) initial requests).primary.Perfect (h+1)) (out : Components α) (cost : Nat),
      Components.Valid (completedDepth reference) (completeRun (h+1) initial requests).primary finalPerfect
        (completeRun (h+1) initial requests).preference out ∧
      GapBST.Storage.Bounded 5 (GapBST.Storage.encode (physicalState (completeRun (h+1) initial requests).primary out)) ∧
      Auxiliary.Metadata.Execution (GapBST.Storage.encode (physicalState initial.primary components)) requests
        (GapBST.Storage.encode (physicalState (completeRun (h+1) initial requests).primary out)) cost ∧
      cost ≤ 7*((memoryCost (memoryKeys initial.primary reference) initial requests + initial.primary.runFlips requests + requests.length) *
          physicalRequestFactor reference)+3*requests.length := by
  obtain ⟨finalPerfect,out,outValid,run⟩ := maintained_physical_run reference initial perfect distinct requests members components valid
  obtain ⟨cost,execution,bound⟩ := GapBST.Storage.services run
  exact ⟨finalPerfect,out,cost,outValid,GapBST.Storage.encode_bounded (physicalState_bounded _ _),execution,bound⟩

end TangoSquared.Paper20261030.SecondaryDecomposition

namespace TangoSquared.Paper20261030.Dyadic

open ColoredStorage Rectangles Secondary SecondaryDecomposition LocalReferences PackedPrimary

theorem metadata_run_robust_bound {h : Nat} (reference : DepthTree 0 h)
    (requests : List Int) (keys : ∀ key ∈ requests, ValidKey (h+1) key) :
    ∃ (after : Source Int (List (Option (Datum Cached)))) (cost : Nat),
      after.shape.leaves = (canonical (h+1) 0).leaves ∧
      GapBST.Storage.Bounded 5 (GapBST.Storage.encode after) ∧
      Auxiliary.Metadata.Execution (GapBST.Storage.encode (initialPhysicalState reference)) requests
        (GapBST.Storage.encode after) cost ∧
      cost ≤ 7*(requests.length+13*robustBound (accessPoints requests)+6*2^(h+1))*physicalRequestFactor reference +
        3*requests.length := by
  let components := initialComponents (completedDepth reference) (canonical (h+1) 0)
    (canonical_perfect (h+1) 0) (fun _ => true)
  have valid := initialComponents_valid (completedDepth reference) (canonical (h+1) 0)
    (canonical_perfect (h+1) 0) (fun _ => true)
  have members : ∀ key ∈ requests, key ∈ (canonical (h+1) 0).leaves :=
    fun key member => (canonical_zero_mem _ _).mpr (keys key member)
  obtain ⟨_,out,_,physical⟩ := maintained_physical_run reference
    (MemoryState.initial (canonical (h+1) 0)) (canonical_perfect (h+1) 0) (canonical_nodup (h+1) 0)
    requests members components valid
  have work := abstract_work_robust_bound reference requests keys
  simp only [abstractWork,PreferredProjection.PrefRouter.depthAccessCount_eq,secondaryCost,MemoryState.initial] at work
  have budget : memoryCost (memoryKeys (canonical (h+1) 0) reference)
      (MemoryState.initial (canonical (h+1) 0)) requests + (canonical (h+1) 0).runFlips requests + requests.length ≤
      requests.length+13*robustBound (accessPoints requests)+6*2^(h+1) := by
    simpa only [MemoryState.initial] using (show _ ≤ _ by omega)
  have charged := physical.mono (Nat.mul_le_mul_right (physicalRequestFactor reference) budget)
  obtain ⟨cost,run,bound⟩ := GapBST.Storage.services charged
  refine ⟨_,cost,?_,GapBST.Storage.encode_bounded (physicalState_bounded _ _),run,?_⟩
  · exact physical.rearranges.leaves.symm.trans (initialPhysicalState_leaves reference)
  · simpa only [Nat.mul_assoc] using bound

end TangoSquared.Paper20261030.Dyadic
