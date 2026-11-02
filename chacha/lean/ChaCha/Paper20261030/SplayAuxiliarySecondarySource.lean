import ChaCha.Paper20261030.SplayAuxiliaryAdapter
import ChaCha.Paper20261030.SplayAuxiliaryReference
import ChaCha.Paper20261030.SplayAuxiliarySourceRotations

/-!
# Secondary access on actual leaf-oriented sources

The source returned here is the same ordinary-splay execution as the raw
BST proof. Its leaf payloads, separators, recursive preferred components,
and global potential inventory are all retained literally.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ColoredStorage RawComponent Decomposition
open MultiSplay.Global.Preferred

@[simp] theorem secondary_source_mapped {a b : Nat} (reference : DepthTree a b)
    (before after : DepthSplit → Bool) :
    (SecondaryDecomposition.source reference before).mapRecords secondaryKey =
      (SecondaryDecomposition.source reference after).mapRecords secondaryKey := by
  induction reference <;>
    simp_all [SecondaryDecomposition.source,Source.mapRecords,secondaryKey]

/-- Total ordinary-splay secondary access with a single persistent forest.
The concrete source rotation trace has exactly the raw rotation count. -/
theorem secondary_source_access {a b : Nat} (reference : DepthTree a b)
    (preference : DepthSplit → Bool) (request : Nat)
    (before : RawComponent Nat Nat)
    (represented : Represents secondaryKey SecondaryDecomposition.followsRight
      (SecondaryDecomposition.source reference preference) before)
    {trees : List (RawTree Nat)}
    (inventory : Core (routerState (Secondary.decodeDepth reference preference))
      (separatorReference reference).toRaw (referenceCuts id before.closed) trees) :
    ∃ after : RawComponent Nat Nat, ∃ next rotations,
      Represents secondaryKey SecondaryDecomposition.followsRight
        (SecondaryDecomposition.source reference (Secondary.intervalUpdate request preference)) after ∧
      Core (routerState (Secondary.decodeDepth reference (Secondary.intervalUpdate request preference)))
        (separatorReference reference).toRaw (referenceCuts id after.closed) next ∧
      SourceRotations before.closed after.closed rotations ∧
      SecondaryExecution reference request (Secondary.decodeDepth reference preference)
        (Secondary.decodeDepth reference (Secondary.intervalUpdate request preference))
          (referenceCuts id before.closed) (referenceCuts id after.closed) rotations ∧
      rotations+2*forestPotential next ≤ 2*forestPotential trees+
        (24*Nat.log 2 (separatorReference reference).height+3)*
          (Secondary.decodeDepth reference preference).accessFlips request := by
  obtain ⟨final,next,rotations,nextInventory,physical,ordinary,bound⟩ :=
    secondary_access reference preference request inventory
  have nextRealizes : MultiSplay.Global.Preferred.Realizes
      (referenceState SecondaryDecomposition.followsRight
        (SecondaryDecomposition.source reference (Secondary.intervalUpdate request preference)))
      (referenceCuts secondaryKey
        (SecondaryDecomposition.source reference (Secondary.intervalUpdate request preference))) final := by
    simpa only [referenceState_secondary,referenceCuts_secondary] using nextInventory.realizes
  obtain ⟨after,afterRep,afterPhysical⟩ := realizes_represented secondaryKey
    SecondaryDecomposition.followsRight _ nextRealizes
  have samePayloads : leafPayloads before.closed = leafPayloads after.closed := by
    rw [represented_leafPayloads represented,represented_leafPayloads afterRep,
      secondary_source_mapped reference preference (Secondary.intervalUpdate request preference)]
  refine ⟨after,next,rotations,afterRep,?_,?_,?_,bound⟩
  · rwa [afterPhysical]
  · apply source_rotations_of_raw
    · rwa [afterPhysical]
    · exact samePayloads
  · rwa [afterPhysical]

end ChaCha.Paper20261030.SplayAuxiliary
