import ChaCha.Paper20261030.MaintainedCompletion

/-!
# Separating the completion root from genuine secondary memories

`completedDepth` adds the manuscript's final depth leaf to the genuine
reference. Its completion access has at most one flip and leaves every
genuine memory cell unchanged. The resulting execution can thus reuse
the existing genuine-memory history accounting across requests.
-/

namespace ChaCha.Paper20261030.LocalReferences

def completedDepth {h : Nat} (reference : DepthTree 0 h) : DepthTree 0 (h+1) :=
  .node h (Nat.zero_le _) (Nat.lt_succ_self _) reference (.leaf (h+1))

theorem completedDepth_shape {h : Nat} (reference : DepthTree 0 h) :
    depthReference (completedDepth reference) = completedReference reference := rfl

end ChaCha.Paper20261030.LocalReferences

namespace ChaCha.Paper20261030.Secondary

open PreferredProjection LocalReferences

variable {α : Type*} [DecidableEq α]

theorem completion_flips_le_one {h : Nat} (reference : DepthTree 0 h) (p : DepthSplit → Bool) :
    (decodeDepth (completedDepth reference) p).accessFlips (h+1) ≤ 1 := by
  have outside : h+1 ∉ (decodeDepth reference p).leaves := by rw [decodeDepth_mem]; omega
  cases bit : p ⟨0,h,h+1⟩ <;>
    simp [completedDepth,decodeDepth,PrefRouter.accessFlips,outside,PrefRouter.leaves,edgeChange,bit]

theorem completed_memoryCost_le {h : Nat} (reference : DepthTree 0 h) (state : MemoryState α) (x : α) :
    memoryCost (memoryKeys state.primary (completedDepth reference)) state [x] ≤
      memoryCost (memoryKeys state.primary reference) state [x]+2 := by
  simp only [memoryCost,Nat.add_zero,completedDepth]
  rw [write_sum_node]
  simp only [PrefRouter.ownerPaths,List.toFinset_cons,List.toFinset_nil,
    Finset.sum_insert (Finset.notMem_empty _),memoryKeys,Finset.sum_empty,Nat.add_zero]
  have root := requestWrites_changes_le_two state.primary x ((⟨0,h,h+1⟩ : DepthSplit),[])
    (state.preference (⟨0,h,h+1⟩,[]))
  omega

theorem completion_preserves_memory {h : Nat} (reference : DepthTree 0 h)
    (primary : PrefRouter α) (memory : MemoryKey → Bool) {key : MemoryKey}
    (member : key ∈ memoryKeys primary reference) :
    advanceDepth primary primary.terminal (h+1) memory key = memory key := by
  have node := ((mem_memoryKeys primary reference key.1 key.2).mp member).1
  have bounds := reference.node_bounds node
  simp [advanceDepth,depthWrite,show ¬ h+1 ≤ key.1.hi by omega]

def MemoryState.completeAdvance (height : Nat) (state : MemoryState α) (x : α) : MemoryState α :=
  let next := state.advance x
  ⟨next.primary,advanceDepth next.primary next.primary.terminal height next.preference⟩

theorem completeAdvance_agrees {h : Nat} (reference : DepthTree 0 h) (state : MemoryState α) (x : α)
    {key : MemoryKey} (member : key ∈ memoryKeys state.primary reference) :
    (state.completeAdvance (h+1) x).preference key = (state.advance x).preference key := by
  apply completion_preserves_memory reference (state.advance x).primary (state.advance x).preference
  simpa only [MemoryState.advance,memoryKeys_access] using member

theorem memoryCost_congr (keys : Finset MemoryKey) (primary : PrefRouter α)
    (before after : MemoryKey → Bool) (same : ∀ key ∈ keys, before key = after key) (requests : List α) :
    memoryCost keys ⟨primary,before⟩ requests = memoryCost keys ⟨primary,after⟩ requests := by
  rw [memoryCost_eq_histories,memoryCost_eq_histories]
  exact Finset.sum_congr rfl (fun key member => by dsimp only; rw [same key member])

theorem completeAdvance_memoryCost {h : Nat} (reference : DepthTree 0 h) (state : MemoryState α)
    (x : α) (requests : List α) :
    memoryCost (memoryKeys state.primary reference) (state.completeAdvance (h+1) x) requests =
      memoryCost (memoryKeys state.primary reference) (state.advance x) requests :=
  memoryCost_congr _ _ _ _ (fun _ member => completeAdvance_agrees reference state x member) requests

end ChaCha.Paper20261030.Secondary
