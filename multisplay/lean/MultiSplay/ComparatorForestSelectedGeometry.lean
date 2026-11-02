import MultiSplay.ComparatorForestPartition
import MultiSplay.ComparatorOwnerMemory

/-! # Owner and endpoint facts derived from the actual selected slots -/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (BST)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

theorem Pair.geometry {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder)) :
    source.rootAddress = componentStart state address ∧
      address.IsPrefix source.endpoint ∧ address.IsPrefix incoming.endpoint := by
  have sourceValid := slots_valid state reference source (before.mem_iff.mpr (by simp))
  have incomingValid := slots_valid state reference incoming (before.mem_iff.mpr (by simp))
  have parkedValid := slots_valid (toggle state address) reference parked (after.mem_iff.mpr (by simp))
  have oldPrefix : address.IsPrefix source.endpoint := by
    rw [← pair.parked_endpoint,parkedValid.continuation,pair.parked_root,List.append_assoc]
    exact List.prefix_append _ _
  have incomingPrefix : address.IsPrefix incoming.endpoint := by
    rw [incomingValid.continuation,pair.incoming_root,List.append_assoc]
    exact List.prefix_append _ _
  refine ⟨?_,oldPrefix,incomingPrefix⟩
  have samePrefix : source.endpoint.take address.length = address.take address.length := by
    obtain ⟨tail,equal⟩ := oldPrefix
    rw [← equal,List.take_left,List.take_length]
  have equal := componentStart_eq_of_take_eq state source.endpoint address address.length samePrefix
    (by rw [sourceValid.start]; exact pair.source_prefix.length_le) (startDepth_le state address)
  exact sourceValid.root_eq.trans equal

theorem Pair.endpoints_distinct {lower upper : Nat} {state : State} {reference : BST lower upper}
    {source incoming : Slot} {remainder : List Slot}
    (before : (slots state reference).Perm (source::incoming::remainder)) :
    source.endpoint ≠ incoming.endpoint := by
  have unique := (before.map Slot.endpoint).nodup (slots_endpoints_nodup state reference)
  have absent := (List.nodup_cons.mp unique).1
  intro equal
  exact absent (by simp [equal])

/-- The indexed source slot carries the very preferred path and guard spine
used by the global chronological event word. -/
theorem Pair.selected_path {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    (real : referenceAt reference.toRaw address ≠ .empty) :
    Path (restrict state source.rootAddress) source.primary.toRaw
      (address.drop (startDepth state address)) (componentSpine state reference.toRaw address)
      (referenceAt reference.toRaw address) := by
  have root := (pair.geometry before after).1
  change source.rootAddress = address.take (startDepth state address) at root
  have located := (slots_valid state reference source (before.mem_iff.mpr (by simp))).located
  have path := ClassicalSwitch.selected_path state address real
  rw [← root,located] at path
  exact path

theorem Pair.eventWord {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder))
    (real : referenceAt reference.toRaw address ≠ .empty) :
    eventWord reference.toRaw state address =
      eventWord source.primary.toRaw (restrict state source.rootAddress)
        (address.drop (startDepth state address)) := by
  have root := (pair.geometry before after).1
  change source.rootAddress = address.take (startDepth state address) at root
  have located := (slots_valid state reference source (before.mem_iff.mpr (by simp))).located
  rw [eventWord_selected state address real,← root,located]

theorem Pair.source_start {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder))
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder)) :
    startDepth state source.endpoint = startDepth state address := by
  have valid := slots_valid state reference source (before.mem_iff.mpr (by simp))
  rw [valid.start,(pair.geometry before after).1]
  exact List.length_take_of_le (startDepth_le state address)

theorem Pair.incoming_start {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (before : (slots state reference).Perm (source::incoming::remainder)) :
    startDepth state incoming.endpoint = address.length + 1 := by
  have valid := slots_valid state reference incoming (before.mem_iff.mpr (by simp))
  rw [valid.start,pair.incoming_root,List.length_append,List.length_singleton]

theorem Pair.tail_bound {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (pair : Pair state address source incoming target parked)
    (after : (slots (toggle state address) reference).Perm (target::parked::remainder)) :
    address.length + 1 ≤ reference.height := by
  have valid := slots_valid (toggle state address) reference parked (after.mem_iff.mpr (by simp))
  have bounded := valid.height
  rw [pair.parked_root,List.length_append,List.length_singleton] at bounded
  omega

end MultiSplay.ComparatorForest
