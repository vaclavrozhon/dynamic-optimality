import MultiSplay.ComparatorForestFrame
import MultiSplay.ComparatorForestSelectedGeometry
import MultiSplay.ComparatorForestInvariant
import MultiSplay.ComparatorProgramChronology
import MultiSplay.ComparatorStableTransaction

/-! # The global comparator service from its concrete selected-pair run

The local execution returns the two maintained suffixes and an exact
classical event word. Slot selection, persistent-memory transfer, unchanged
component framing and the global invariant are discharged here.
-/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open TangoSquared Paper20261030
open Primary (Key)
open EndpointEncoding ClassicalSwitch CommonForest
open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition ComparatorStableSuffix
open ComparatorSuffix (writeGenuine)
open Secondary (spliceBits)

structure PairExecution {lower upper : Nat} (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (scale : Nat)
    (state : State) (memory : Memory) (family : Family) (pivot : Key)
    (source incoming target parked : Slot) (main tail : Component) (work : Nat) : Prop where
  mainBound : startDepth state pivot ≤ reference.height
  tailBound : pivot.length+1 ≤ reference.height
  mainRep : Represents followsRight
    (suffixSource secondary (bits (startDepth state pivot)
      (spliceBits pivot.length
        (writeGenuine (startDepth state pivot) pivot.length (localMemory memory source.endpoint))
        (localMemory memory incoming.endpoint)))
      (startDepth state pivot) ⟨Nat.zero_le _,mainBound⟩) main
  tailRep : Represents followsRight
    (suffixSource secondary (bits (pivot.length+1) (localMemory memory source.endpoint))
      (pivot.length+1) ⟨Nat.zero_le _,tailBound⟩) tail
  program : Program [projectedTree state family source,projectedTree state family incoming]
    (eventWord reference.toRaw state pivot)
    [projectedTree (toggle state pivot) (family.replace source.endpoint incoming.endpoint main tail) target,
      projectedTree (toggle state pivot) (family.replace source.endpoint incoming.endpoint main tail) parked] work
  paid : work ≤ scale * (ComparatorHistory.eventCost secondary memory (state,pivot)+1) * seamFactor secondary

def PairService {lower upper : Nat} (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (scale : Nat) : Prop :=
  ∀ state memory family pivot source incoming target parked remainder,
    referenceAt reference.toRaw pivot ≠ .empty →
    family.Valid secondary state reference memory →
    Pair state pivot source incoming target parked →
    (slots state reference).Perm (source::incoming::remainder) →
    (slots (toggle state pivot) reference).Perm (target::parked::remainder) →
    ∃ main tail work,
      PairExecution reference secondary scale state memory family pivot source incoming target parked main tail work

theorem pairExecution_valid {lower upper : Nat} {reference : BST lower upper}
    {secondary : DepthTree 0 reference.height} {scale : Nat}
    {state : State} {memory : Memory} {family : Family} {pivot : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    {main tail : Component} {work : Nat}
    (valid : family.Valid secondary state reference memory)
    (pair : Pair state pivot source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state pivot) reference).Perm (target::parked::remainder))
    (run : PairExecution reference secondary scale state memory family pivot source incoming target parked main tail work) :
    (family.replace source.endpoint incoming.endpoint main tail).Valid secondary
      (toggle state pivot) reference (ComparatorHistory.update (state,pivot) memory) := by
  obtain ⟨root,oldPrefix,incomingPrefix⟩ := pair.geometry before after
  exact valid.replace_of_partition pivot source incoming target parked remainder before after root
    (by rw [pair.target_eq]) pair.parked_root (by rw [pair.target_eq]) pair.parked_endpoint
    oldPrefix incomingPrefix main tail run.mainBound run.tailBound run.mainRep run.tailRep

theorem pairExecution_program {lower upper : Nat} {reference : BST lower upper}
    {secondary : DepthTree 0 reference.height} {scale : Nat}
    {state : State} {memory : Memory} {family : Family} {pivot : Key}
    {source incoming target parked : Slot} {remainder : List Slot}
    {main tail : Component} {work : Nat}
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state pivot) reference).Perm (target::parked::remainder))
    (run : PairExecution reference secondary scale state memory family pivot source incoming target parked main tail work) :
    Program (projectedForest state reference family) (eventWord reference.toRaw state pivot)
      (projectedForest (toggle state pivot) reference
        (family.replace source.endpoint incoming.endpoint main tail)) work := by
  apply program_of_partition reference state (toggle state pivot) family _ source incoming target parked remainder before after
    (localRun := run.program)
  intro slot member
  have unique : (source.endpoint::incoming.endpoint::remainder.map Slot.endpoint).Nodup := by
    simpa only [List.map_cons] using (before.map Slot.endpoint).nodup (slots_endpoints_nodup state reference)
  have oldAbsent := (List.nodup_cons.mp unique).1
  have incomingAbsent := (List.nodup_cons.mp (List.nodup_cons.mp unique).2).1
  have oldDifferent : slot.endpoint ≠ source.endpoint := by
    intro same
    exact oldAbsent (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨slot,member,same⟩))
  have incomingDifferent : slot.endpoint ≠ incoming.endpoint := by
    intro same
    exact incomingAbsent (List.mem_map.mpr ⟨slot,member,same⟩)
  exact (Family.replace_other family source.endpoint incoming.endpoint main tail slot.endpoint
    oldDifferent incomingDifferent).symm

theorem service_of_pairService {lower upper : Nat} (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (scale : Nat)
    (localService : PairService reference secondary scale) :
    ComparatorHistory.Service secondary reference.toRaw (scale * seamFactor secondary)
      (Maintained reference secondary) := by
  intro state memory before pivot valid real
  obtain ⟨family,familyValid,rfl⟩ := valid
  obtain ⟨source,incoming,target,parked,remainder,oldSlots,newSlots,pair⟩ :=
    selected_partition state reference pivot real
  obtain ⟨main,tail,work,run⟩ := localService state memory family pivot source incoming target parked remainder
    real familyValid pair oldSlots newSlots
  let next := family.replace source.endpoint incoming.endpoint main tail
  refine ⟨projectedForest (toggle state pivot) reference next,work,
    ⟨next,pairExecution_valid familyValid pair oldSlots newSlots run,rfl⟩,
    pairExecution_program oldSlots newSlots run,?_⟩
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using run.paid

end MultiSplay.ComparatorForest
