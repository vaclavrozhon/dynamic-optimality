import ChaCha.Paper20261030.SplayAuxiliaryCompletion
import ChaCha.Paper20261030.SplayAuxiliaryGlobalSearchDepth

/-! A complete request consists of the actual primary head loop and the
completion secondary access. The potential is shared across requests;
no auxiliary is reset between successive accesses. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality.SearchRotation
open ColoredStorage PreferredProjection Secondary LocalReferences

variable {α : Type*} [DecidableEq α]

def requestFactor {height : Nat} (reference : DepthTree 0 height) : Nat :=
  3*headFactor (completedDepth reference)

inductive RequestExecution {height : Nat} (reference : DepthTree 0 height)
    (initial : MemoryState α) (request : α) (components : Global.Table α) : Global.Table α → Prop
  | run {middle out : Global.Table α}
      (heads : HeadLoopExecution (completedDepth reference) request initial components
        (initial.primary.exitDepths request) (initial.advance request) middle)
      (completion : CompletionExecution (completedDepth reference) (initial.primary.access request)
        (initial.advance request).preference middle out) : RequestExecution reference initial request components out

 theorem request_rotations {height : Nat} (reference : DepthTree 0 height)
    (initial : MemoryState α) (request : α) (perfect : initial.primary.Perfect (height+1))
    (distinct : initial.primary.leaves.Nodup) (components : Global.Table α)
    (valid : Global.Table.Valid (completedDepth reference) initial.primary perfect initial.preference components) :
    ∃ (out : Global.Table α) (rotations : Nat),
      Global.Table.Valid (completedDepth reference) (initial.primary.access request)
        (PrefRouter.perfect_access perfect request) (initial.completeAdvance (height+1) request).preference out ∧
      Rotations (GapBST.encode (Physical.physicalState initial.primary components))
        (GapBST.encode (Physical.physicalState (initial.primary.access request) out)) rotations ∧
      RequestExecution reference initial request components out ∧
      rotations+408*out.potential (initial.primary.access request).leaves.toFinset ≤
        408*components.potential initial.primary.leaves.toFinset+
          (memoryCost (memoryKeys initial.primary reference) initial [request]+initial.primary.accessFlips request+1)*
            requestFactor reference := by
  obtain ⟨middle,first,middleValid,firstPhysical,firstOrdinary,firstBound⟩ :=
    access_head_loop_exists (completedDepth reference) initial request perfect distinct components valid
  have middlePerfect := PrefRouter.perfect_access perfect request
  have middleDistinct : (initial.primary.access request).leaves.Nodup := by
    rw [PrefRouter.access_leaves]
    exact distinct
  obtain ⟨out,last,outValid,lastPhysical,lastOrdinary,lastBound⟩ :=
    completion_exists (completedDepth reference) (initial.primary.access request) middlePerfect middleDistinct
      (initial.advance request).preference middle middleValid
  have completion := completion_flips_le_one reference
    (ownerBits (initial.primary.access request) (initial.primary.access request).terminal (initial.advance request).preference)
  have completionCharge := Nat.mul_le_mul_right (headFactor (completedDepth reference)) completion
  have memory := completed_memoryCost_le reference initial request
  have memoryCharge := Nat.mul_le_mul_right (headFactor (completedDepth reference)) memory
  refine ⟨out,first+last,outValid,firstPhysical.append lastPhysical,.run firstOrdinary lastOrdinary,?_⟩
  unfold requestFactor
  nlinarith

 theorem physical_endpoint_depth [LinearOrder α] {height : Nat} (reference : DepthTree 0 height)
    (primary : PrefRouter α) (perfect : primary.Perfect height) (ordered : primary.leaves.Pairwise (· < ·))
    (memory : MemoryKey → Bool) (components : Global.Table α)
    (valid : Global.Table.Valid reference primary perfect memory components) :
    ∃ depth ≤ 1, MTR.Tree.searchDepth primary.terminal
      (GapBST.encode (Physical.physicalState primary components)) = some depth := by
  have distinct := ordered.nodup
  have physicalOrdered : MTR.Tree.Ordered (GapBST.encode (Physical.physicalState primary components)) := by
    unfold MTR.Tree.Ordered
    rw [GapBST.encode_word,Physical.physical_leaves reference perfect distinct memory components valid]
    exact ordered
  change MTR.Tree.Ordered (GapBST.encode (PrimaryPhysical.expand _ _ primary)) at physicalOrdered
  rw [PrimaryPhysical.expand] at physicalOrdered
  change ∃ depth ≤ 1, MTR.Tree.searchDepth primary.terminal
    (GapBST.encode (PrimaryPhysical.expand _ _ primary)) = some depth
  rw [PrimaryPhysical.expand]
  exact Global.component_bottom_searchDepth _ _ _ _ physicalOrdered

/-- Includes the successful search in the actual initial tree. -/
theorem request_access [LinearOrder α] {height : Nat} (reference : DepthTree 0 height)
    (initial : MemoryState α) (request : α) (perfect : initial.primary.Perfect (height+1))
    (ordered : initial.primary.leaves.Pairwise (· < ·)) (member : request ∈ initial.primary.leaves)
    (components : Global.Table α)
    (valid : Global.Table.Valid (completedDepth reference) initial.primary perfect initial.preference components) :
    ∃ (out : Global.Table α) (cost : Nat),
      Global.Table.Valid (completedDepth reference) (initial.primary.access request)
        (PrefRouter.perfect_access perfect request) (initial.completeAdvance (height+1) request).preference out ∧
      Access request (GapBST.encode (Physical.physicalState initial.primary components))
        (GapBST.encode (Physical.physicalState (initial.primary.access request) out)) cost ∧
      RequestExecution reference initial request components out ∧
      cost+816*out.potential (initial.primary.access request).leaves.toFinset ≤
        816*components.potential initial.primary.leaves.toFinset+
          (memoryCost (memoryKeys initial.primary reference) initial [request]+initial.primary.accessFlips request+1)*
            (2*requestFactor reference+2) := by
  have distinct : initial.primary.leaves.Nodup := ordered.imp (fun smaller => ne_of_lt smaller)
  obtain ⟨out,rotations,outValid,physical,ordinary,bound⟩ :=
    request_rotations reference initial request perfect distinct components valid
  have afterOrdered : (initial.primary.access request).leaves.Pairwise (· < ·) := by
    rw [PrefRouter.access_leaves]
    exact ordered
  obtain ⟨depth,depthBound,searched⟩ := physical_endpoint_depth (completedDepth reference)
    (initial.primary.access request) (PrefRouter.perfect_access perfect request) afterOrdered
      (initial.completeAdvance (height+1) request).preference out outValid
  rw [PrefRouter.terminal_access request initial.primary member] at searched
  have beforeOrdered : MTR.Tree.Ordered (GapBST.encode (Physical.physicalState initial.primary components)) := by
    unfold MTR.Tree.Ordered
    rw [GapBST.encode_word,Physical.physical_leaves (completedDepth reference) perfect distinct _ _ valid]
    exact ordered
  obtain ⟨cost,access,costBound⟩ := RawDepth.access_of_final_depth physical beforeOrdered request searched
  exact ⟨out,cost,outValid,access,ordinary,by nlinarith⟩

end ChaCha.Paper20261030.SplayAuxiliary
