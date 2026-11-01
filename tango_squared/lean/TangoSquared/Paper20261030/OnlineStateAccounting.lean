import TangoSquared.Paper20261030.OnlineStateSpecification

/-! The same flip and geometric accounting for the fixed, prefix-consistent
state specification. This charges the selected metadata executions, not
an independently chosen offline trace for each complete request word. -/

namespace TangoSquared.Paper20261030.OnlineSpecification

open ColoredStorage PreferredProjection Secondary SecondaryDecomposition LocalReferences Rectangles

variable {α : Type*} [DecidableEq α] {h : Nat}

theorem run_cost {reference : DepthTree 0 h} {keyWord : List α}
    (distinct : keyWord.Nodup) (state : State reference keyWord) (requests : List (Fin keyWord.length)) :
    (run distinct state requests).2 ≤
      7*((memoryCost (memoryKeys state.memory.primary reference) state.memory (requests.map (key keyWord)) +
        state.memory.primary.runFlips (requests.map (key keyWord)) + requests.length)*physicalRequestFactor reference) +
      3*requests.length := by
  induction requests generalizing state with
  | nil => simp [run,memoryCost,PrefRouter.runFlips]
  | cons request requests ih =>
    have first := (step distinct state request).bound
    have last := ih (step distinct state request).after
    rw [(step distinct state request).memory] at last
    change (run distinct (step distinct state request).after requests).2 ≤
      7*((memoryCost (memoryKeys (state.memory.primary.access (key keyWord request)) reference)
        (state.memory.completeAdvance (h+1) (key keyWord request)) (requests.map (key keyWord)) +
        (state.memory.primary.access (key keyWord request)).runFlips (requests.map (key keyWord)) +
        requests.length)*physicalRequestFactor reference)+3*requests.length at last
    rw [memoryKeys_access,completeAdvance_memoryCost] at last
    change (step distinct state request).cost + (run distinct (step distinct state request).after requests).2 ≤ _
    simp only [State.budget,memoryCost,List.map_cons,PrefRouter.runFlips,List.length_cons,
      Nat.add_zero,Nat.zero_add,Nat.mul_add,Nat.add_mul,Nat.one_mul] at first last ⊢
    omega

noncomputable def canonicalState (reference : DepthTree 0 h) : State reference (Dyadic.canonical (h+1) 0).leaves := {
  memory := MemoryState.initial (Dyadic.canonical (h+1) 0)
  perfect := Dyadic.canonical_perfect _ _
  components := initialComponents (completedDepth reference) (Dyadic.canonical (h+1) 0)
    (Dyadic.canonical_perfect _ _) (fun _ => true)
  valid := initialComponents_valid _ _ _ _
  word := rfl }

theorem canonical_cost (reference : DepthTree 0 h)
    (requests : List (Fin (Dyadic.canonical (h+1) 0).leaves.length)) :
    (run (Dyadic.canonical_nodup _ _) (canonicalState reference) requests).2 ≤
      7*(requests.length+13*Rectangles.robustBound (accessPoints (requests.map (key (Dyadic.canonical (h+1) 0).leaves)))+
        6*2^(h+1))*physicalRequestFactor reference+3*requests.length := by
  have bound := run_cost (Dyadic.canonical_nodup (h+1) 0) (canonicalState reference) requests
  have valid : ∀ x ∈ requests.map (key (Dyadic.canonical (h+1) 0).leaves), Dyadic.ValidKey (h+1) x := by
    intro x member
    obtain ⟨request,_,rfl⟩ := List.mem_map.mp member
    exact (Dyadic.canonical_zero_mem _ _).mp (List.getElem_mem _)
  have work := Dyadic.abstract_work_robust_bound reference _ valid
  simp only [Dyadic.abstractWork,PrefRouter.depthAccessCount_eq,secondaryCost,MemoryState.initial,List.length_map] at work
  have coefficient : memoryCost (memoryKeys (Dyadic.canonical (h+1) 0) reference)
      (MemoryState.initial (Dyadic.canonical (h+1) 0)) (requests.map (key (Dyadic.canonical (h+1) 0).leaves)) +
      (Dyadic.canonical (h+1) 0).runFlips (requests.map (key (Dyadic.canonical (h+1) 0).leaves)) + requests.length ≤
      requests.length+13*Rectangles.robustBound (accessPoints (requests.map (key (Dyadic.canonical (h+1) 0).leaves)))+6*2^(h+1) := by
    simpa only [MemoryState.initial] using (show _ ≤ _ by omega)
  exact bound.trans (by
    simpa only [canonicalState,MemoryState.initial,Nat.mul_assoc] using
      Nat.add_le_add_right (Nat.mul_le_mul_left 7 (Nat.mul_le_mul_right (physicalRequestFactor reference) coefficient)) (3*requests.length))

end TangoSquared.Paper20261030.OnlineSpecification
