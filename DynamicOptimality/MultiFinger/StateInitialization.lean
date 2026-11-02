import DynamicOptimality.MultiFinger.State
import DynamicOptimality.MultiFinger.HandMovesMarkers

/-! # Initial states for the actual occupied source positions

The permanent reference-root mark contributes at most one extra occupied
key. Coincident fingers are counted only once by the compressed hand.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR

variable {reference : RawTree Nat} {count : Nat}

def Configuration.markerList (state : Configuration reference count) : List Nat :=
  reference.rootKey.toList ++ (List.finRange count).flatMap
    (fun index => (state.finger index).focus.rootKey.toList)

theorem Configuration.marked_markerList (state : Configuration reference count) :
    state.marked = fun key => decide (key ∈ state.markerList) := by
  classical
  funext key
  simp [Configuration.marked,Configuration.markerList]

private theorem option_flatMap_length {β : Type*} (items : List β) (value : β → Option Nat) :
    (items.flatMap (fun item => (value item).toList)).length ≤ items.length := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [Option.toList] at ih
    cases shape : value item <;> simp only [List.flatMap_cons,shape,Option.toList,
      List.length_append,List.length_cons,List.length_nil] <;> omega

theorem Configuration.markerList_length (state : Configuration reference count) :
    state.markerList.length ≤ count+1 := by
  have others := option_flatMap_length (List.finRange count)
    (fun index => (state.finger index).focus.rootKey)
  simp only [List.length_finRange] at others
  have root : reference.rootKey.toList.length ≤ 1 := by cases reference.rootKey <;> simp
  simp only [markerList,List.length_append]
  omega

noncomputable def Configuration.hand (state : Configuration reference count) : Hand Nat :=
  Hand.compress state.marked reference

theorem Configuration.hand_source (state : Configuration reference count) :
    state.hand.source = reference := Hand.compress_source _ _

theorem Configuration.hand_size (state : Configuration reference count)
    (distinct : reference.inorder.Nodup) : state.hand.core.size ≤ 2*(count+1) := by
  change (Hand.compress state.marked reference).core.size ≤ _
  rw [Hand.compress_core,state.marked_markerList]
  exact (Steiner.size_le_fingers state.markerList reference distinct).trans
    (Nat.mul_le_mul_left 2 state.markerList_length)

private theorem mem_plug {tree : RawTree Nat} {key : Nat} (member : key ∈ tree.inorder)
    (frames : List (Pointer.Frame Nat)) : key ∈ (Pointer.plug tree frames).inorder := by
  induction frames generalizing tree with
  | nil => exact member
  | cons frame frames ih =>
    cases frame <;> apply ih <;>
      simp only [Tree.inorder,List.mem_append,List.mem_singleton] <;> tauto

theorem Configuration.hand_finger (state : Configuration reference count) (index : Fin count)
    {key : Nat} (found : (state.finger index).focus.rootKey = some key) :
    key ∈ state.hand.core.inorder := by
  have focusMem : key ∈ (state.finger index).focus.inorder := by
    cases shape : (state.finger index).focus with
    | empty => simp [shape,Tree.rootKey] at found
    | node left pivot right =>
      have same : pivot = key := by simpa only [shape,Tree.rootKey,Option.some.injEq] using found
      subst pivot
      simp [Tree.inorder]
  have wholeMem : key ∈ (state.finger index).tree.inorder := by
    exact mem_plug focusMem (state.finger index).ancestors
  rw [state.valid index] at wholeMem
  change key ∈ (Hand.compress state.marked reference).core.inorder
  rw [Hand.compress_core]
  exact Steiner.retains state.marked reference wholeMem (state.marked_finger index found)

theorem Configuration.initialize_state (state : Configuration reference count)
    (distinct : reference.inorder.Nodup) :
    ∃ physical : State state.hand,
      physical.credit ≤ 20*(count+1)*Nat.log 2 (10*(count+1))+4*reference.size := by
  obtain ⟨physical,paid⟩ := State.initialization state.hand
  have core := state.hand_size distinct
  have logarithm : Nat.log 2 (5*state.hand.core.size) ≤ Nat.log 2 (10*(count+1)) :=
    Nat.log_mono_right (by omega)
  have product := Nat.mul_le_mul core logarithm
  rw [state.hand_source] at paid
  exact ⟨physical,by nlinarith⟩

end DynamicOptimality.MultiFinger
