import MultiSplay.ComparatorForestEndpoints
import MultiSplay.ComparatorOwnerMemory
import MultiSplay.ClassicalSwitchMarkedUpdate

/-!
# Validity of the persistent comparator family

Each actual preferred-component slot is represented by its maintained suffix
source, read from the global original-owner memory. The representation includes
its height bound. It therefore makes no assertion vacuous for out-of-range
starts. Switch updates replace only the two selected endpoint components.
-/

namespace MultiSplay.ClassicalSwitch

open ChaCha.Primary (Key)
open EndpointEncoding

/-- The last nonpreferred boundary in a concatenated route is either inside
the suffix, or the original component start when the suffix is preferred. -/
theorem startDepth_append (state : State) (route suffix : Key) :
    startDepth state (route ++ suffix) =
      if startDepth (restrict state route) suffix = 0 then startDepth state route
      else route.length + startDepth (restrict state route) suffix := by
  induction route generalizing state with
  | nil =>
      simp only [List.nil_append, restrict, startDepth, List.length_nil, Nat.zero_add]
      split <;> simp_all
  | cons edge route ih =>
      by_cases zero : startDepth (restrict (below state edge) route) suffix = 0
      · simp only [List.cons_append, restrict, startDepth, ih, if_pos zero]
      · have positive : 0 < route.length + startDepth (restrict (below state edge) route) suffix := by omega
        simp only [List.cons_append, restrict, startDepth, ih, if_neg zero, List.length_cons,
          if_neg (show ¬(route.length + startDepth (restrict (below state edge) route) suffix = 0 ∧
            state [] = edge) by omega)]
        omega

theorem startDepth_toggle_self (state : State) (pivot : Key) :
    startDepth (toggle state pivot) pivot = startDepth state pivot := by
  induction pivot generalizing state with
  | nil => rfl
  | cons edge rest ih =>
      simp only [startDepth, below_toggle_cons, ih]
      simp [toggle]

/-- A preferred continuation below either pivot child starts at the old
component root or exactly at this child, according to the pivot's old bit. -/
theorem startDepth_child_preferred (state : State) (pivot : Key) (side : Bool) (rest : Key)
    (follows : RootPreferred (restrict state (pivot ++ [side])) rest) :
    startDepth state (pivot ++ (side :: rest)) =
      if state pivot = side then startDepth state pivot else pivot.length + 1 := by
  have tailStart : startDepth (below (restrict state pivot) side) rest = 0 := by
    simpa only [restrict_append, restrict] using (startDepth_zero _ _).mpr follows
  have head : restrict state pivot [] = state pivot := by simp only [restrict_eq, List.append_nil]
  rw [startDepth_append]
  by_cases same : state pivot = side <;>
    simp [startDepth, tailStart, head, same]

theorem startDepth_old_endpoint (state : State) (pivot rest : Key)
    (follows : RootPreferred (restrict state (pivot ++ [state pivot])) rest) :
    startDepth state (pivot ++ (state pivot :: rest)) = startDepth state pivot := by
  simpa using startDepth_child_preferred state pivot (state pivot) rest follows

theorem startDepth_incoming_endpoint (state : State) (pivot rest : Key)
    (follows : RootPreferred (restrict state (pivot ++ [!(state pivot)])) rest) :
    startDepth state (pivot ++ ((!(state pivot)) :: rest)) = pivot.length + 1 := by
  simpa using startDepth_child_preferred state pivot (!(state pivot)) rest follows

theorem startDepth_toggle_old_endpoint (state : State) (pivot rest : Key)
    (follows : RootPreferred (restrict state (pivot ++ [state pivot])) rest) :
    startDepth (toggle state pivot) (pivot ++ (state pivot :: rest)) = pivot.length + 1 := by
  have follows' : RootPreferred (restrict (toggle state pivot) (pivot ++ [state pivot])) rest := by
    rwa [restrict_toggle_child]
  simpa [toggle] using startDepth_child_preferred (toggle state pivot) pivot (state pivot) rest follows'

theorem startDepth_toggle_incoming_endpoint (state : State) (pivot rest : Key)
    (follows : RootPreferred (restrict state (pivot ++ [!(state pivot)])) rest) :
    startDepth (toggle state pivot) (pivot ++ ((!(state pivot)) :: rest)) = startDepth state pivot := by
  have follows' : RootPreferred (restrict (toggle state pivot) (pivot ++ [!(state pivot)])) rest := by
    rwa [restrict_toggle_child]
  have result := startDepth_child_preferred (toggle state pivot) pivot (!(state pivot)) rest follows'
  rw [startDepth_toggle_self] at result
  simpa [toggle] using result

end MultiSplay.ClassicalSwitch

namespace MultiSplay.ComparatorForest

open DynamicOptimality (BST)
open ChaCha
open Paper20261030
open Primary (Key)
open EndpointEncoding ClassicalSwitch
open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition
open ComparatorStableSuffix (bits)
open Secondary (spliceBits)
open ComparatorSuffix (writeGenuine)

def RepresentsAt {height : Nat} (secondary : DepthTree 0 height) (state : State)
    (memory : Memory) (endpoint : Key) (component : Component) : Prop :=
  ∃ bound : startDepth state endpoint ≤ height,
    Represents followsRight
      (suffixSource secondary (bits (startDepth state endpoint) (localMemory memory endpoint))
        (startDepth state endpoint) ⟨Nat.zero_le _,bound⟩) component

/-- The actual maintained source at every current canonical component slot. -/
def Family.Valid {height lower upper : Nat} (secondary : DepthTree 0 height)
    (state : State) (reference : BST lower upper) (memory : Memory) (family : Family) : Prop :=
  ∀ slot ∈ slots state reference, RepresentsAt secondary state memory slot.endpoint (family slot.endpoint)

theorem Family.Valid.bound {height lower upper : Nat} {secondary : DepthTree 0 height}
    {state : State} {reference : BST lower upper} {memory : Memory} {family : Family}
    (valid : family.Valid secondary state reference memory)
    {slot : Slot} (member : slot ∈ slots state reference) : startDepth state slot.endpoint ≤ height :=
  (valid slot member).choose

theorem Family.Valid.represents {height lower upper : Nat} {secondary : DepthTree 0 height}
    {state : State} {reference : BST lower upper} {memory : Memory} {family : Family}
    (valid : family.Valid secondary state reference memory)
    {slot : Slot} (member : slot ∈ slots state reference) (bound : startDepth state slot.endpoint ≤ height) :
    Represents followsRight
      (suffixSource secondary (bits (startDepth state slot.endpoint) (localMemory memory slot.endpoint))
        (startDepth state slot.endpoint) ⟨Nat.zero_le _,bound⟩) (family slot.endpoint) :=
  (valid slot member).choose_spec

theorem initial_valid {lower upper : Nat} (state : State) (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (memory : Memory) :
    (initialFamily secondary state memory).Valid secondary state reference memory := by
  intro slot member
  have valid := slots_valid state reference slot member
  have bound : startDepth state slot.endpoint ≤ reference.height := by
    have within := valid.within_height
    omega
  exact ⟨bound, initialFamily_represents secondary state memory slot.endpoint bound⟩

theorem Family.Valid.projected_domains {lower upper : Nat} {state : State}
    {reference : BST lower upper} {secondary : DepthTree 0 reference.height}
    {memory : Memory} {family : Family} (valid : family.Valid secondary state reference memory) :
    CommonForest.domains (projectedForest state reference family) =
      CommonForest.domains (forest state reference.toRaw) := by
  rw [← slots_keys state reference]
  unfold CommonForest.domains projectedForest
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro slot member
  have located := slots_valid state reference slot member
  exact ComparatorPrimary.stable_projected_inorder (restrict state slot.rootAddress) slot.primary
    secondary (startDepth state slot.endpoint) ⟨Nat.zero_le _,valid.bound member⟩
    (localMemory memory slot.endpoint) (family slot.endpoint)
    (valid.represents member (valid.bound member)) located.within_height

theorem representsAt_main {height : Nat} (secondary : DepthTree 0 height)
    (state : State) (pivot oldEndpoint incomingEndpoint : Key) (memory : Memory)
    (main : Component) (bound : startDepth state pivot ≤ height)
    (oldPrefix : pivot.IsPrefix oldEndpoint) (incomingPrefix : pivot.IsPrefix incomingEndpoint)
    (newStart : startDepth (toggle state pivot) incomingEndpoint = startDepth state pivot)
    (represented : Represents followsRight
      (suffixSource secondary (bits (startDepth state pivot)
        (spliceBits pivot.length
          (writeGenuine (startDepth state pivot) pivot.length (localMemory memory oldEndpoint))
          (localMemory memory incomingEndpoint)))
        (startDepth state pivot) ⟨Nat.zero_le _,bound⟩) main) :
    RepresentsAt secondary (toggle state pivot) (ComparatorHistory.update (state,pivot) memory)
      incomingEndpoint main := by
  have memoryEq := ComparatorHistory.update_main (state,pivot) memory oldEndpoint incomingEndpoint
    oldPrefix incomingPrefix
  change localMemory (ComparatorHistory.update (state,pivot) memory) incomingEndpoint =
    spliceBits pivot.length
      (writeGenuine (startDepth state pivot) pivot.length (localMemory memory oldEndpoint))
      (localMemory memory incomingEndpoint) at memoryEq
  refine ⟨by rw [newStart]; exact bound, ?_⟩
  simpa only [newStart, memoryEq] using represented

theorem representsAt_parked {height : Nat} (secondary : DepthTree 0 height)
    (state : State) (pivot oldEndpoint : Key) (memory : Memory)
    (parked : Component) (bound : pivot.length + 1 ≤ height)
    (newStart : startDepth (toggle state pivot) oldEndpoint = pivot.length + 1)
    (represented : Represents followsRight
      (suffixSource secondary (bits (pivot.length+1) (localMemory memory oldEndpoint))
        (pivot.length+1) ⟨Nat.zero_le _,bound⟩) parked) :
    RepresentsAt secondary (toggle state pivot) (ComparatorHistory.update (state,pivot) memory)
      oldEndpoint parked := by
  have memoryEq := ComparatorHistory.bits_update_parked (state,pivot) memory oldEndpoint
  change bits (pivot.length+1) (localMemory (ComparatorHistory.update (state,pivot) memory) oldEndpoint) =
    bits (pivot.length+1) (localMemory memory oldEndpoint) at memoryEq
  refine ⟨by rw [newStart]; exact bound, ?_⟩
  simpa only [newStart, memoryEq] using represented

theorem RepresentsAt.other {height : Nat} {secondary : DepthTree 0 height}
    {state : State} {memory : Memory} {endpoint : Key} {component : Component}
    (represented : RepresentsAt secondary state memory endpoint component) (pivot : Key)
    (sameStart : startDepth (toggle state pivot) endpoint = startDepth state endpoint)
    (different : componentStart state endpoint ≠ componentStart state pivot) :
    RepresentsAt secondary (toggle state pivot) (ComparatorHistory.update (state,pivot) memory)
      endpoint component := by
  obtain ⟨bound,represented⟩ := represented
  have memoryEq := ComparatorHistory.bits_update_other_component state pivot endpoint memory different
  change bits (startDepth state endpoint)
      (localMemory (ComparatorHistory.update (state,pivot) memory) endpoint) =
    bits (startDepth state endpoint) (localMemory memory endpoint) at memoryEq
  refine ⟨by rw [sameStart]; exact bound, ?_⟩
  simpa only [sameStart, memoryEq] using represented

def Family.replace (family : Family) (oldEndpoint incomingEndpoint : Key)
    (main parked : Component) : Family := fun endpoint =>
  if endpoint = incomingEndpoint then main
  else if endpoint = oldEndpoint then parked else family endpoint

@[simp] theorem Family.replace_incoming (family : Family) (oldEndpoint incomingEndpoint : Key)
    (main parked : Component) :
    family.replace oldEndpoint incomingEndpoint main parked incomingEndpoint = main := by
  simp [Family.replace]

theorem Family.replace_old (family : Family) (oldEndpoint incomingEndpoint : Key)
    (main parked : Component) (different : oldEndpoint ≠ incomingEndpoint) :
    family.replace oldEndpoint incomingEndpoint main parked oldEndpoint = parked := by
  simp [Family.replace, different]

theorem Family.replace_other (family : Family) (oldEndpoint incomingEndpoint : Key)
    (main parked : Component) (endpoint : Key)
    (oldDifferent : endpoint ≠ oldEndpoint) (incomingDifferent : endpoint ≠ incomingEndpoint) :
    family.replace oldEndpoint incomingEndpoint main parked endpoint = family endpoint := by
  simp [Family.replace, oldDifferent, incomingDifferent]

/-- The two local transaction outputs preserve the entire family. The
premises describe only the literal selected-slot partition and local source
representations. Distinctness and every unchanged-component memory frame are
derived from the canonical slots and global owner-update definitions. -/
theorem Family.Valid.replace_of_partition {height lower upper : Nat}
    {secondary : DepthTree 0 height} {state : State} {reference : BST lower upper}
    {memory : Memory} {family : Family} (valid : family.Valid secondary state reference memory)
    (pivot : Key) (old incoming next parked : Slot) (rest : List Slot)
    (oldOrder : (slots state reference).Perm (old :: incoming :: rest))
    (newOrder : (slots (toggle state pivot) reference).Perm (next :: parked :: rest))
    (oldRoot : old.rootAddress = componentStart state pivot)
    (nextRoot : next.rootAddress = old.rootAddress)
    (parkedRoot : parked.rootAddress = pivot ++ [state pivot])
    (nextEndpoint : next.endpoint = incoming.endpoint)
    (parkedEndpoint : parked.endpoint = old.endpoint)
    (oldPrefix : pivot.IsPrefix old.endpoint) (incomingPrefix : pivot.IsPrefix incoming.endpoint)
    (main tail : Component) (mainBound : startDepth state pivot ≤ height)
    (tailBound : pivot.length + 1 ≤ height)
    (mainRep : Represents followsRight
      (suffixSource secondary (bits (startDepth state pivot)
        (spliceBits pivot.length
          (writeGenuine (startDepth state pivot) pivot.length (localMemory memory old.endpoint))
          (localMemory memory incoming.endpoint)))
        (startDepth state pivot) ⟨Nat.zero_le _,mainBound⟩) main)
    (tailRep : Represents followsRight
      (suffixSource secondary (bits (pivot.length+1) (localMemory memory old.endpoint))
        (pivot.length+1) ⟨Nat.zero_le _,tailBound⟩) tail) :
    (family.replace old.endpoint incoming.endpoint main tail).Valid secondary
      (toggle state pivot) reference (ComparatorHistory.update (state,pivot) memory) := by
  have endpointUnique : (old.endpoint :: incoming.endpoint :: rest.map Slot.endpoint).Nodup := by
    simpa only [List.map_cons] using (oldOrder.map Slot.endpoint).nodup (slots_endpoints_nodup state reference)
  have oldAbsent := (List.nodup_cons.mp endpointUnique).1
  have incomingAbsent := (List.nodup_cons.mp (List.nodup_cons.mp endpointUnique).2).1
  have endpointDifferent : old.endpoint ≠ incoming.endpoint := by
    intro same
    exact oldAbsent (by simp only [List.mem_cons, same, true_or])
  have rootUnique : (old.rootAddress :: incoming.rootAddress :: rest.map Slot.rootAddress).Nodup := by
    simpa only [List.map_cons] using (oldOrder.map Slot.rootAddress).nodup (slots_roots_nodup state reference)
  have rootAbsent := (List.nodup_cons.mp rootUnique).1
  have rootLength : old.rootAddress.length = startDepth state pivot := by
    rw [oldRoot]
    exact List.length_take_of_le (startDepth_le state pivot)
  have nextMember : next ∈ slots (toggle state pivot) reference := newOrder.mem_iff.mpr (by simp)
  have parkedMember : parked ∈ slots (toggle state pivot) reference := newOrder.mem_iff.mpr (by simp)
  have nextStart : startDepth (toggle state pivot) incoming.endpoint = startDepth state pivot := by
    have start := (slots_valid (toggle state pivot) reference next nextMember).start
    rwa [nextEndpoint, nextRoot, rootLength] at start
  have parkedStart : startDepth (toggle state pivot) old.endpoint = pivot.length + 1 := by
    have start := (slots_valid (toggle state pivot) reference parked parkedMember).start
    simpa only [parkedEndpoint, parkedRoot, List.length_append, List.length_singleton] using start
  intro slot member
  rcases List.mem_cons.mp (newOrder.mem_iff.mp member) with rfl | memberTail
  · rw [nextEndpoint, Family.replace_incoming]
    exact representsAt_main secondary state pivot old.endpoint incoming.endpoint memory main mainBound
      oldPrefix incomingPrefix nextStart mainRep
  · rcases List.mem_cons.mp memberTail with rfl | inRest
    · rw [parkedEndpoint, Family.replace_old _ _ _ _ _ endpointDifferent]
      exact representsAt_parked secondary state pivot old.endpoint memory tail tailBound parkedStart tailRep
    · have oldMember : slot ∈ slots state reference := oldOrder.mem_iff.mpr (by simp [inRest])
      have oldDifferent : slot.endpoint ≠ old.endpoint := by
        intro same
        exact oldAbsent (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨slot,inRest,same⟩))
      have incomingDifferent : slot.endpoint ≠ incoming.endpoint := by
        intro same
        exact incomingAbsent (List.mem_map.mpr ⟨slot,inRest,same⟩)
      have rootDifferent : slot.rootAddress ≠ old.rootAddress := by
        intro same
        exact rootAbsent (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨slot,inRest,same⟩))
      have oldValid := slots_valid state reference slot oldMember
      have newValid := slots_valid (toggle state pivot) reference slot member
      have sameStart : startDepth (toggle state pivot) slot.endpoint = startDepth state slot.endpoint :=
        newValid.start.trans oldValid.start.symm
      have different : componentStart state slot.endpoint ≠ componentStart state pivot := by
        intro same
        exact rootDifferent (oldValid.root_eq.trans (same.trans oldRoot.symm))
      rw [Family.replace_other _ _ _ _ _ _ oldDifferent incomingDifferent]
      exact (valid slot oldMember).other pivot sameStart different

end MultiSplay.ComparatorForest
