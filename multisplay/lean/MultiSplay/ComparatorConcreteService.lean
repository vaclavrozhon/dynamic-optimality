import MultiSplay.ComparatorForestService
import MultiSplay.ComparatorForestIndexedAlignment
import MultiSplay.ComparatorGuardStableService

/-!
# The concrete maintained classical comparator service

The selected canonical slots determine the exact indexed pivot and children.
The maintained local service therefore applies without a geometric or cheap
comparator hypothesis. Its two output sources are installed at their actual
endpoint addresses; the forest service supplies the unchanged component frame.
-/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open TangoSquared Paper20261030
open Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest
open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition ComparatorStableSuffix PrimaryWings

private theorem execution_of_indexed {lower upper bottom key top : Nat}
    (reference : BST lower upper) (secondary : DepthTree 0 reference.height)
    (state : State) (memory : Memory) (family : Family) (pivot : Key)
    (source incoming target parked : Slot) (remainder : List Slot)
    (real : referenceAt reference.toRaw pivot ≠ .empty)
    (valid : family.Valid secondary state reference memory)
    (pair : Pair state pivot source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state pivot) reference).Perm (target::parked::remainder))
    {left : BST bottom key} {right : BST (key+1) top}
    (path : ComparatorGuard.IndexedPath (restrict state source.rootAddress) source.primary
      (pivot.drop (startDepth state pivot)) (componentSpine state reference.toRaw pivot) (.node left right)) :
    ∃ main tail work,
      PairExecution reference secondary 100000000 state memory family pivot source incoming target parked main tail work := by
  let start := startDepth state pivot
  let relative := pivot.drop start
  have depth : start+relative.length = pivot.length := by
    simp only [relative,List.length_drop]
    exact Nat.add_sub_of_le (startDepth_le state pivot)
  have sourceMember : source ∈ slots state reference := before.mem_iff.mpr (by simp)
  have incomingMember : incoming ∈ slots state reference := before.mem_iff.mpr (by simp)
  have targetMember : target ∈ slots (toggle state pivot) reference := after.mem_iff.mpr (by simp)
  have parkedMember : parked ∈ slots (toggle state pivot) reference := after.mem_iff.mpr (by simp)
  have sourceStart := pair.source_start before after
  have incomingStart := pair.incoming_start before
  have tailBound := pair.tail_bound after
  have mainBound : start ≤ reference.height := (startDepth_le state pivot).trans (by omega)
  have upperBound : start+relative.length < reference.height := by omega
  have represented : Represents followsRight
      (suffixSource secondary (bits start (localMemory memory source.endpoint)) start
        ⟨Nat.zero_le _,mainBound⟩) (family source.endpoint) := by
    simpa only [sourceStart] using valid.represents sourceMember (valid.bound sourceMember)
  have incomingRep : Represents followsRight
      (suffixSource secondary (bits (start+relative.length+1) (localMemory memory incoming.endpoint))
        (start+relative.length+1) ⟨Nat.zero_le _,by omega⟩) (family incoming.endpoint) := by
    simpa only [incomingStart,depth] using valid.represents incomingMember (valid.bound incomingMember)
  have localSide : restrict (restrict state source.rootAddress) relative [] = state pivot := by
    rw [pair.local_state before after]
    simp only [restrict_eq,List.append_nil]
  have coverage := pair.child_coverage before after path
  have oldEnough : (exits (ComparatorGuard.childRouter (restrict (restrict state source.rootAddress) relative)
      left right ((restrict (restrict state source.rootAddress) relative) []))).length ≤
      reference.height+1-(start+relative.length+1) := by
    rw [localSide,depth]
    dsimp only [relative,start]
    omega
  have incomingEnough : (exits (ComparatorGuard.childRouter (restrict (restrict state source.rootAddress) relative)
      left right (!((restrict (restrict state source.rootAddress) relative) [])))).length ≤
      reference.height+1-(start+relative.length+1) := by
    rw [localSide,depth]
    dsimp only [relative,start]
    omega
  obtain ⟨main,tail,work,mainRep,tailRep,program,paid⟩ := ComparatorGuard.stable_service (address := relative) path secondary start
    upperBound (localMemory memory source.endpoint) (localMemory memory incoming.endpoint)
    (family source.endpoint) (family incoming.endpoint) represented incomingRep oldEnough incomingEnough
  change start+relative.length = pivot.length at depth
  simp only [depth] at mainRep tailRep program paid
  rw [localSide] at program
  have targetStart : startDepth (toggle state pivot) target.endpoint = start := by
    rw [(slots_valid (toggle state pivot) reference target targetMember).start,pair.target_eq]
    change source.rootAddress.length = start
    rw [← (slots_valid state reference source sourceMember).start,sourceStart]
  have parkedStart : startDepth (toggle state pivot) parked.endpoint = pivot.length+1 := by
    rw [(slots_valid (toggle state pivot) reference parked parkedMember).start,
      pair.parked_root,List.length_append,List.length_singleton]
  have distinct := Pair.endpoints_distinct before
  have children := pair.child_projections before after path (pivot.length+1)
    (ComparatorRecords.erase (closed (family incoming.endpoint))) (ComparatorRecords.erase (closed tail))
  have sourceTree : projectedTree state family source = ComparatorPrimary.projectedTree
      (restrict state source.rootAddress) source.primary start (ComparatorRecords.erase (closed (family source.endpoint))) := by
    simp only [projectedTree,sourceStart,start]
  have incomingTree : projectedTree state family incoming = GapBST.gaps (ComparatorPrimary.projected (pivot.length+1)
      (ComparatorGuard.childRouter (restrict (restrict state source.rootAddress) relative) left right (!(state pivot)))
      (ComparatorRecords.erase (closed (family incoming.endpoint)))) := by
    unfold projectedTree
    rw [incomingStart]
    exact children.1
  have targetTree : projectedTree (toggle state pivot) (family.replace source.endpoint incoming.endpoint main tail) target =
      ComparatorPrimary.projectedTree (toggle (restrict state source.rootAddress) relative) source.primary start
        (ComparatorRecords.erase (closed main)) := by
    have nextStart : startDepth (toggle state pivot) incoming.endpoint = start := by
      simpa only [pair.target_eq] using targetStart
    rw [pair.target_eq]
    change ComparatorPrimary.projectedTree (restrict (toggle state pivot) source.rootAddress) source.primary
      (startDepth (toggle state pivot) incoming.endpoint)
      (ComparatorRecords.erase (closed (family.replace source.endpoint incoming.endpoint main tail incoming.endpoint))) = _
    rw [Family.replace_incoming,nextStart,pair.local_toggle before after]
  have parkedTree : projectedTree (toggle state pivot) (family.replace source.endpoint incoming.endpoint main tail) parked =
      GapBST.gaps (ComparatorPrimary.projected (pivot.length+1)
        (ComparatorGuard.childRouter (restrict (restrict state source.rootAddress) relative) left right (state pivot))
        (ComparatorRecords.erase (closed tail))) := by
    unfold projectedTree
    rw [parkedStart,pair.parked_endpoint,Family.replace_old _ _ _ _ _ distinct]
    exact children.2
  rw [← sourceTree,← incomingTree,← targetTree,← parkedTree,← pair.eventWord before after real] at program
  have eventCost := ComparatorHistory.eventCost_eq_genuine secondary memory (state,pivot) source.endpoint
    (pair.geometry before after).2.1
  change ComparatorHistory.eventCost secondary memory (state,pivot) =
    ComparatorSuffix.genuineCost secondary start pivot.length (localMemory memory source.endpoint) at eventCost
  rw [← eventCost] at paid
  exact ⟨main,tail,work,mainBound,tailBound,mainRep,tailRep,program,paid⟩

/-- Every selected classical switch has its actual maintained comparator
program, with a uniform constant and the original global owner-memory cost. -/
theorem concrete_pair_service {lower upper : Nat} (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) : PairService reference secondary 100000000 := by
  intro state memory family pivot source incoming target parked remainder real valid pair before after
  obtain ⟨bottom,top,focus,path,same⟩ := ComparatorGuard.indexedPath_of_raw source.primary
    (pair.selected_path before after real)
  cases focus with
  | empty boundary => exact False.elim (real same.symm)
  | @node bottom key top left right =>
      exact execution_of_indexed reference secondary state memory family pivot source incoming target parked remainder
        real valid pair before after path

end MultiSplay.ComparatorForest
