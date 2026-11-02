import ChaCha.Paper20261030.MaintainedPhysicalHeadStep
import ChaCha.Paper20261030.SecondaryAccessAccounting

/-!
# The complete maintained physical head-switch loop

Each counted head step is realized on the original-key physical tree.
The component invariant is passed to the next step, and all secondary
flips are charged to the existing persistent-memory write count.
This loop stops at the requested primary endpoint; resetting the
completion port and serving that original key are subsequent operations.
-/

namespace ChaCha.PreferredProjection.PrefRouter

variable {α : Type*} [DecidableEq α]

theorem HeadStep.ownerPaths {x : α} {d : Nat} {before after : PrefRouter α}
    (step : HeadStep x d before after) (depth : Nat) : after.ownerPaths depth = before.ownerPaths depth := by
  induction step generalizing depth with
  | leftRoot => cases depth <;> rfl
  | rightRoot => cases depth <;> rfl
  | leftDown right step ih => cases depth <;> simp only [PrefRouter.ownerPaths,ih]
  | rightDown left outside step ih => cases depth <;> simp only [PrefRouter.ownerPaths,ih]

end ChaCha.PreferredProjection.PrefRouter

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem head_memoryKeys {x : α} {d a b : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) (reference : DepthTree a b) :
    memoryKeys after reference = memoryKeys before reference := by
  induction reference with
  | leaf => rfl
  | node cut lower upper left right ihl ihr => simp only [memoryKeys,step.ownerPaths,ihl,ihr]

theorem depthCost_path_congr {before after : PrefRouter α} {x : α}
    (same : before.searchPath x = after.searchPath x) (keys : Finset MemoryKey)
    (depths : List Nat) (memory : MemoryKey → Bool) :
    depthCost keys before x depths memory = depthCost keys after x depths memory := by
  have advanceSame : ∀ d pref, advanceDepth before x d pref = advanceDepth after x d pref := by
    intro d pref
    funext key
    simp only [advanceDepth,depthWrite_path_congr same]
  induction depths generalizing memory with
  | nil => rfl
  | cons d ds ih => simp only [depthCost,depthWrite_path_congr same,advanceSame,ih]

end ChaCha.Paper20261030.Secondary

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage SourcePointer PreferredProjection Secondary

variable {α : Type*} [DecidableEq α]

theorem maintained_head_loop {height : Nat} (reference : DepthTree 0 height)
    {x : α} {initial final : MemoryState α} {depths : List Nat}
    (trace : SequentialHeadTrace x initial depths final)
    (perfect : initial.primary.Perfect height) (distinct : initial.primary.leaves.Nodup)
    (components : Components α) (valid : Components.Valid reference initial.primary perfect initial.preference components) :
    ∃ (finalPerfect : final.primary.Perfect height) (out : Components α),
      Components.Valid reference final.primary finalPerfect final.preference out ∧
      Rearranges (physicalState initial.primary components) (physicalState final.primary out)
        ((depthCost (memoryKeys initial.primary reference) initial.primary x depths initial.preference + depths.length) *
          physicalHeadBound reference) := by
  induction trace generalizing components with
  | nil state =>
    refine ⟨perfect,components,valid,?_⟩
    intro ancestors
    exact ⟨[],0,.nil _,Nat.zero_le _⟩
  | @cons before middle preference final depth depths step rest ih =>
    have afterPerfect := step.perfect perfect
    have afterDistinct : middle.leaves.Nodup := by rw [step.leaves]; exact distinct
    obtain ⟨next,nextValid,first⟩ := maintained_physical_head reference step perfect distinct preference components valid
    obtain ⟨finalPerfect,out,outValid,last⟩ := ih afterPerfect afterDistinct next nextValid
    have flips := head_flips_le_writes reference step perfect distinct (Nat.le_refl height) preference
    have firstBound := first.mono (Nat.mul_le_mul_right (physicalHeadBound reference) (Nat.add_le_add_right flips 1))
    have keySame := head_memoryKeys step reference
    have costSame := depthCost_path_congr (step.searchPath x) (memoryKeys before reference) depths
      (advanceDepth before x depth preference)
    simp only [keySame,costSame] at last
    refine ⟨finalPerfect,out,outValid,?_⟩
    have joined := firstBound.trans last
    simpa only [depthCost,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using joined

theorem maintained_access_head_loop {height : Nat} (reference : DepthTree 0 height)
    (initial : MemoryState α) (x : α) (perfect : initial.primary.Perfect height)
    (distinct : initial.primary.leaves.Nodup) (components : Components α)
    (valid : Components.Valid reference initial.primary perfect initial.preference components) :
    ∃ out : Components α,
      Components.Valid reference (initial.primary.access x) (PrefRouter.perfect_access perfect x)
        (initial.advance x).preference out ∧
      Rearranges (physicalState initial.primary components) (physicalState (initial.primary.access x) out)
        ((memoryCost (memoryKeys initial.primary reference) initial [x] + initial.primary.accessFlips x) *
          physicalHeadBound reference) := by
  obtain ⟨finalPerfect,out,outValid,execution⟩ := maintained_head_loop reference
    (access_sequential_headTrace initial x) perfect distinct components valid
  refine ⟨out,outValid,?_⟩
  simpa only [sequentialRequest_cost,PrefRouter.exitDepths_length,MemoryState.advance] using execution

end ChaCha.Paper20261030.SecondaryDecomposition
