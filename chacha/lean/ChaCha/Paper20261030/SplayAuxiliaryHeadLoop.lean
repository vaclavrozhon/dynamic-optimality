import ChaCha.Paper20261030.SplayAuxiliaryHead
import ChaCha.Paper20261030.MaintainedHeadLoop

/-! The entire primary head loop retains its actual ordinary-splay
certificates and telescopes one persistent global potential. -/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality.SearchRotation
open ColoredStorage PreferredProjection Secondary

variable {α : Type*} [DecidableEq α]

inductive HeadLoopExecution {height : Nat} (reference : DepthTree 0 height) (request : α) :
    MemoryState α → Global.Table α → List Nat → MemoryState α → Global.Table α → Prop
  | nil (state : MemoryState α) (components : Global.Table α) :
      HeadLoopExecution reference request state components [] state components
  | cons {before middle : PrefRouter α} {memory : MemoryKey → Bool} {final : MemoryState α}
      {depth : Nat} {depths : List Nat} {components next out : Global.Table α}
      (step : PrefRouter.HeadStep request depth before middle)
      (head : HeadExecution reference memory before middle depth components next)
      (rest : HeadLoopExecution reference request ⟨middle,advanceDepth before request depth memory⟩ next depths final out) :
      HeadLoopExecution reference request ⟨before,memory⟩ components (depth::depths) final out

 theorem head_loop_exists {height : Nat} (reference : DepthTree 0 height)
    {request : α} {initial final : MemoryState α} {depths : List Nat}
    (trace : SequentialHeadTrace request initial depths final)
    (perfect : initial.primary.Perfect height) (distinct : initial.primary.leaves.Nodup)
    (components : Global.Table α) (valid : Global.Table.Valid reference initial.primary perfect initial.preference components) :
    ∃ (finalPerfect : final.primary.Perfect height) (out : Global.Table α) (rotations : Nat),
      Global.Table.Valid reference final.primary finalPerfect final.preference out ∧
      Rotations (GapBST.encode (Physical.physicalState initial.primary components))
        (GapBST.encode (Physical.physicalState final.primary out)) rotations ∧
      HeadLoopExecution reference request initial components depths final out ∧
      rotations+408*out.potential final.primary.leaves.toFinset ≤
        408*components.potential initial.primary.leaves.toFinset+
          (depthCost (memoryKeys initial.primary reference) initial.primary request depths initial.preference+depths.length)*
            headFactor reference := by
  induction trace generalizing components with
  | nil state => exact ⟨perfect,components,0,valid,.refl _,.nil _ _,by simp [depthCost]⟩
  | @cons before middle preference final depth depths step rest ih =>
      have afterPerfect := step.perfect perfect
      have afterDistinct : middle.leaves.Nodup := by rw [step.leaves]; exact distinct
      obtain ⟨next,first, nextValid,firstPhysical,firstOrdinary,firstBound⟩ :=
        head_exists reference step perfect distinct preference components valid
      obtain ⟨finalPerfect,out,last,outValid,lastPhysical,lastOrdinary,lastBound⟩ :=
        ih afterPerfect afterDistinct next nextValid
      have flips := head_flips_le_writes reference step perfect distinct (Nat.le_refl height) preference
      have firstCharge := Nat.mul_le_mul_right (headFactor reference) (Nat.add_le_add_right flips 1)
      have keySame := head_memoryKeys step reference
      have costSame := depthCost_path_congr (step.searchPath request) (memoryKeys before reference) depths
        (advanceDepth before request depth preference)
      simp only [keySame,costSame] at lastBound
      refine ⟨finalPerfect,out,first+last,outValid,firstPhysical.append lastPhysical,
        .cons step firstOrdinary lastOrdinary,?_⟩
      simp only [depthCost,List.length_cons,Nat.add_mul,Nat.one_mul] at firstBound lastBound firstCharge ⊢
      omega

 theorem access_head_loop_exists {height : Nat} (reference : DepthTree 0 height)
    (initial : MemoryState α) (request : α) (perfect : initial.primary.Perfect height)
    (distinct : initial.primary.leaves.Nodup) (components : Global.Table α)
    (valid : Global.Table.Valid reference initial.primary perfect initial.preference components) :
    ∃ out : Global.Table α, ∃ rotations : Nat,
      Global.Table.Valid reference (initial.primary.access request) (PrefRouter.perfect_access perfect request)
        (initial.advance request).preference out ∧
      Rotations (GapBST.encode (Physical.physicalState initial.primary components))
        (GapBST.encode (Physical.physicalState (initial.primary.access request) out)) rotations ∧
      HeadLoopExecution reference request initial components (initial.primary.exitDepths request) (initial.advance request) out ∧
      rotations+408*out.potential (initial.primary.access request).leaves.toFinset ≤
        408*components.potential initial.primary.leaves.toFinset+
          (memoryCost (memoryKeys initial.primary reference) initial [request]+initial.primary.accessFlips request)*
            headFactor reference := by
  obtain ⟨finalPerfect,out,rotations,outValid,physical,ordinary,bound⟩ :=
    head_loop_exists reference (access_sequential_headTrace initial request) perfect distinct components valid
  refine ⟨out,rotations,outValid,physical,ordinary,?_⟩
  simpa only [sequentialRequest_cost,PrefRouter.exitDepths_length,MemoryState.advance] using bound

end ChaCha.Paper20261030.SplayAuxiliary
