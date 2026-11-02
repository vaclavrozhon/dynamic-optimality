import ChaCha.Paper20261030.MaintainedPhysicalRequest
import ChaCha.Paper20261030.SourceServices

/-!
# Whole request histories in the maintained physical representation

Completion resets preserve genuine memories. Consequently a sequence of
the actual physical request traces is charged to the original global
memory-change and primary-flip counts, with one additional unit per key.
-/

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection

variable {α : Type*} [DecidableEq α]

def completeRun (height : Nat) (initial : MemoryState α) : List α → MemoryState α
  | [] => initial
  | key :: requests => completeRun height (initial.completeAdvance height key) requests

theorem completeRun_primary (height : Nat) (initial : MemoryState α) (requests : List α) :
    (completeRun height initial requests).primary = initial.primary.run requests := by
  induction requests generalizing initial with
  | nil => rfl
  | cons key requests ih =>
    simpa only [completeRun,MemoryState.completeAdvance,MemoryState.advance,PrefRouter.run] using
      ih (initial.completeAdvance height key)

end ChaCha.Paper20261030.Secondary

namespace ChaCha.Paper20261030.SecondaryDecomposition

open ColoredStorage SourcePointer PreferredProjection Secondary LocalReferences

variable {α : Type*} [DecidableEq α]

theorem maintained_physical_run {h : Nat} (reference : DepthTree 0 h)
    (initial : MemoryState α) (perfect : initial.primary.Perfect (h+1)) (distinct : initial.primary.leaves.Nodup)
    (requests : List α) (members : ∀ key ∈ requests, key ∈ initial.primary.leaves)
    (components : Components α)
    (valid : Components.Valid (completedDepth reference) initial.primary perfect initial.preference components) :
    ∃ (finalPerfect : (completeRun (h+1) initial requests).primary.Perfect (h+1)) (out : Components α),
      Components.Valid (completedDepth reference) (completeRun (h+1) initial requests).primary finalPerfect
        (completeRun (h+1) initial requests).preference out ∧
      Services (physicalState initial.primary components) requests
        (physicalState (completeRun (h+1) initial requests).primary out)
        ((memoryCost (memoryKeys initial.primary reference) initial requests + initial.primary.runFlips requests + requests.length) *
          physicalRequestFactor reference) := by
  induction requests generalizing initial components with
  | nil => exact ⟨perfect,components,valid,.nil _ _⟩
  | cons key requests ih =>
    have member := members key (by simp)
    obtain ⟨next,nextValid,first⟩ := maintained_physical_request reference initial perfect distinct key member components valid
    let nextState := initial.completeAdvance (h+1) key
    have nextPerfect : nextState.primary.Perfect (h+1) := PrefRouter.perfect_access perfect key
    have nextDistinct : nextState.primary.leaves.Nodup := by
      change (initial.primary.access key).leaves.Nodup
      rw [PrefRouter.access_leaves]
      exact distinct
    have nextMembers : ∀ x ∈ requests, x ∈ nextState.primary.leaves := by
      intro x hx
      change x ∈ (initial.primary.access key).leaves
      rw [PrefRouter.access_leaves]
      exact members x (by simp [hx])
    obtain ⟨finalPerfect,out,outValid,last⟩ := ih nextState nextPerfect nextDistinct nextMembers next nextValid
    have nextPrimary : nextState.primary = initial.primary.access key := rfl
    rw [nextPrimary,memoryKeys_access] at last
    change Services _ requests _
      ((memoryCost (memoryKeys initial.primary reference) (initial.completeAdvance (h+1) key) requests +
        (initial.primary.access key).runFlips requests + requests.length) * physicalRequestFactor reference) at last
    rw [completeAdvance_memoryCost] at last
    refine ⟨finalPerfect,out,outValid,Services.cons first last ?_⟩
    simp only [memoryCost,PrefRouter.runFlips,List.length_cons,Nat.add_zero,Nat.zero_add,Nat.add_mul,
      Nat.zero_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.le_refl]

end ChaCha.Paper20261030.SecondaryDecomposition
