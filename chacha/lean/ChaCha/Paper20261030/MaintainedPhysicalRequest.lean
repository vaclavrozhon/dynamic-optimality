import ChaCha.Paper20261030.CompletedDepthAccounting

/-!
# One whole original-key request with the persistent invariant

The head loop, completion reset, and original-key visit are composed into
one root-returning physical service trace. Its bound uses only the existing
genuine-memory cost, actual primary flips, and one unit for the request.
-/

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage SourcePointer PreferredProjection Secondary LocalReferences

variable {α : Type*} [DecidableEq α]

def physicalRequestFactor {h : Nat} (reference : DepthTree 0 h) : Nat :=
  10000000 * (Nat.clog 2 ((depthReference (completedDepth reference)).height+1)+1)

theorem maintained_physical_request {h : Nat} (reference : DepthTree 0 h)
    (initial : MemoryState α) (perfect : initial.primary.Perfect (h+1)) (distinct : initial.primary.leaves.Nodup)
    (x : α) (member : x ∈ initial.primary.leaves) (components : Components α)
    (valid : Components.Valid (completedDepth reference) initial.primary perfect initial.preference components) :
    ∃ out : Components α,
      Components.Valid (completedDepth reference) (initial.primary.access x) (PrefRouter.perfect_access perfect x)
        (initial.completeAdvance (h+1) x).preference out ∧
      VisitsLeaf x (physicalState initial.primary components) (physicalState (initial.primary.access x) out)
        ((memoryCost (memoryKeys initial.primary reference) initial [x]+initial.primary.accessFlips x+1) *
          physicalRequestFactor reference) := by
  obtain ⟨middle,middleValid,headTrace⟩ := maintained_access_head_loop (completedDepth reference) initial x
    perfect distinct components valid
  have afterDistinct : (initial.primary.access x).leaves.Nodup := by rw [PrefRouter.access_leaves]; exact distinct
  obtain ⟨out,outValid,completionTrace⟩ := maintained_completion (completedDepth reference) (initial.primary.access x)
    (PrefRouter.perfect_access perfect x) afterDistinct (initial.advance x).preference middle middleValid
  have endpoint := PrefRouter.terminal_access x initial.primary member
  rw [endpoint] at completionTrace
  have memoryBound := completed_memoryCost_le reference initial x
  have completionBound := completion_flips_le_one reference
    (ownerBits (initial.primary.access x) (initial.primary.access x).terminal (initial.advance x).preference)
  rw [endpoint] at completionBound
  refine ⟨out,outValid,(completionTrace.prepend headTrace).mono ?_⟩
  unfold physicalHeadBound physicalRequestFactor
  nlinarith

end ChaCha.Paper20261030.SecondaryDecomposition
