import MultiSplay.ComparatorVirtualProjection
import MultiSplay.ComparatorGenuineHistory
import MultiSplay.ClassicalSwitchAccounting

/-!
# Indexed preferred components and their persistent initial suffixes

Each slot names an actual indexed reference subtree and the external address
at which its preferred path ends. The endpoint, rather than the component
root, indexes the maintained secondary component. The finite slot list has
exactly the canonical preferred-forest order, including empty components.
-/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open TangoSquared
open Paper20261030
open Primary (Key)
open EndpointEncoding ClassicalSwitch
open ColoredStorage AuxiliaryComponent BoundaryObservations PathDecomposition
open SecondaryDecomposition

/-- The actual external endpoint reached by following current preferences. -/
def finish : State → RawTree Nat → Key
  | _, .empty => []
  | state, .node left _ right =>
      if state [] then true :: finish (below state true) right
      else false :: finish (below state false) left

theorem finish_follows (state : State) (reference : RawTree Nat) :
    RootPreferred state (finish state reference) := by
  induction reference generalizing state with
  | empty => exact rootPreferred_nil _
  | node left key right ihl ihr =>
      cases side : state [] with
      | false =>
          simpa only [finish,side,Bool.false_eq_true,if_false] using
            (rootPreferred_cons state false _).mpr ⟨side,ihl _⟩
      | true =>
          simpa only [finish,side,if_true] using
            (rootPreferred_cons state true _).mpr ⟨side,ihr _⟩

theorem finish_start (state : State) (reference : RawTree Nat) :
    startDepth state (finish state reference) = 0 :=
  (startDepth_zero _ _).mpr (finish_follows state reference)

theorem finish_external (state : State) (reference : RawTree Nat) :
    referenceAt reference (finish state reference) = .empty := by
  induction reference generalizing state with
  | empty => rfl
  | node left key right ihl ihr =>
      cases side : state [] <;> simp only [finish,side,Bool.false_eq_true,if_false,if_true,
        referenceAt,ihl,ihr]

theorem finish_length {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (finish state reference.toRaw).length =
      (PrimaryWings.exits (ComparatorPrimary.routing state reference)).length := by
  induction reference generalizing state with
  | empty => rfl
  | node left right ihl ihr =>
      cases side : state [] <;>
        simp [DynamicOptimality.BST.toRaw,finish,ComparatorPrimary.routing,PrimaryWings.exits,side,ihl,ihr]

theorem finish_height {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (finish state reference.toRaw).length ≤ reference.height := by
  induction reference generalizing state with
  | empty => exact le_rfl
  | node left right ihl ihr =>
      have leftBound := ihl (below state false)
      have rightBound := ihr (below state true)
      cases side : state [] <;>
        simp only [DynamicOptimality.BST.toRaw,finish,side,Bool.false_eq_true,if_false,if_true,
          List.length_cons,Splay.Tree.BST.height] <;> omega

structure Slot where
  lower : Nat
  upper : Nat
  primary : BST lower upper
  rootAddress : Key
  endpoint : Key

def Slot.lift (edge : Bool) (slot : Slot) : Slot :=
  { slot with rootAddress := edge :: slot.rootAddress, endpoint := edge :: slot.endpoint }

def rootSlot {lower upper : Nat} (state : State) (reference : BST lower upper) : Slot :=
  ⟨lower,upper,reference,[],finish state reference.toRaw⟩

def otherSlots : {lower upper : Nat} → State → BST lower upper → List Slot
  | _,_,_,.empty _ => []
  | _,_,state,.node left right =>
      (if state [] then (rootSlot (below state false) left).lift false
        else (rootSlot (below state true) right).lift true) ::
      ((otherSlots (below state false) left).map (Slot.lift false) ++
        (otherSlots (below state true) right).map (Slot.lift true))

def slots {lower upper : Nat} (state : State) (reference : BST lower upper) : List Slot :=
  rootSlot state reference :: otherSlots state reference

def Slot.keys (state : State) (slot : Slot) : RawTree Nat :=
  preferred (restrict state slot.rootAddress) slot.primary.toRaw

@[simp] theorem Slot.keys_lift (state : State) (edge : Bool) (slot : Slot) :
    (slot.lift edge).keys state = slot.keys (below state edge) := rfl

@[simp] theorem rootSlot_keys {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (rootSlot state reference).keys state = preferred state reference.toRaw := rfl

theorem otherSlots_keys {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (otherSlots state reference).map (Slot.keys state) = otherComponents state reference.toRaw := by
  induction reference generalizing state with
  | empty => rfl
  | node left right ihl ihr =>
      cases side : state [] <;>
        simp [otherSlots,otherComponents,DynamicOptimality.BST.toRaw,side,List.map_map,
          Function.comp_def,ihl,ihr]

theorem slots_keys {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (slots state reference).map (Slot.keys state) = forest state reference.toRaw := by
  simp only [slots,List.map_cons,rootSlot_keys,otherSlots_keys,forest]

/-- Every component root and endpoint are derived from the same actual
reference. In particular the stored root is the last nonpreferred boundary
on this endpoint's route, not a freely chosen owner. -/
structure Slot.Valid {lower upper : Nat} (state : State) (reference : BST lower upper)
    (slot : Slot) : Prop where
  located : referenceAt reference.toRaw slot.rootAddress = slot.primary.toRaw
  continuation : slot.endpoint = slot.rootAddress ++
    finish (restrict state slot.rootAddress) slot.primary.toRaw
  start : startDepth state slot.endpoint = slot.rootAddress.length
  height : slot.rootAddress.length + slot.primary.height ≤ reference.height

theorem rootSlot_valid {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (rootSlot state reference).Valid state reference :=
  ⟨rfl,rfl,finish_start state reference.toRaw,by simp [rootSlot]⟩

theorem Slot.Valid.lift {lower upper childLower childUpper : Nat}
    {state : State} {reference : BST lower upper} {child : BST childLower childUpper}
    {edge : Bool} {slot : Slot}
    (valid : slot.Valid (below state edge) child)
    (located : referenceAt reference.toRaw [edge] = child.toRaw)
    (height : child.height + 1 ≤ reference.height)
    (boundary : state [] ≠ edge ∨ 0 < slot.rootAddress.length) :
    (slot.lift edge).Valid state reference := by
  refine ⟨?_,?_,?_,?_⟩
  · change referenceAt reference.toRaw ([edge] ++ slot.rootAddress) = slot.primary.toRaw
    rw [referenceAt_append,located]
    exact valid.located
  · simpa only [Slot.lift,List.cons_append,restrict] using congrArg (List.cons edge) valid.continuation
  · have outside : ¬ (slot.rootAddress.length = 0 ∧ state [] = edge) := by
      rcases boundary with different | nonempty
      · exact fun condition => different condition.2
      · omega
    simp only [Slot.lift,startDepth,valid.start,if_neg outside,List.length_cons]
  · have childBound := valid.height
    simp only [Slot.lift,List.length_cons]
    omega

theorem otherSlots_valid {lower upper : Nat} (state : State) (reference : BST lower upper) :
    ∀ slot ∈ otherSlots state reference,
      slot.Valid state reference ∧ 0 < slot.rootAddress.length := by
  induction reference generalizing state with
  | empty => simp [otherSlots]
  | @node lower key upper left right ihl ihr =>
      intro slot member
      have leftHeight : left.height + 1 ≤ (Splay.Tree.BST.node left right).height := by
        simp only [Splay.Tree.BST.height]; omega
      have rightHeight : right.height + 1 ≤ (Splay.Tree.BST.node left right).height := by
        simp only [Splay.Tree.BST.height]; omega
      simp only [otherSlots,List.mem_cons,List.mem_append] at member
      rcases member with rfl | inLeft | inRight
      · cases side : state [] with
        | false =>
            simp only [side,Bool.false_eq_true,if_false]
            exact ⟨(rootSlot_valid (below state true) right).lift rfl rightHeight
              (Or.inl (by simp [side])),by simp [Slot.lift,rootSlot]⟩
        | true =>
            simp only [side,if_true]
            exact ⟨(rootSlot_valid (below state false) left).lift rfl leftHeight
              (Or.inl (by simp [side])),by simp [Slot.lift,rootSlot]⟩
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp inLeft
        obtain ⟨valid,nonempty⟩ := ihl (below state false) child present
        exact ⟨valid.lift rfl leftHeight (Or.inr nonempty),by simp [Slot.lift]⟩
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp inRight
        obtain ⟨valid,nonempty⟩ := ihr (below state true) child present
        exact ⟨valid.lift rfl rightHeight (Or.inr nonempty),by simp [Slot.lift]⟩

theorem slots_valid {lower upper : Nat} (state : State) (reference : BST lower upper) :
    ∀ slot ∈ slots state reference, slot.Valid state reference := by
  intro slot member
  rcases List.mem_cons.mp member with rfl | other
  · exact rootSlot_valid state reference
  · exact (otherSlots_valid state reference slot other).1

theorem Slot.Valid.root_eq {lower upper : Nat} {state : State} {reference : BST lower upper}
    {slot : Slot} (valid : slot.Valid state reference) :
    slot.rootAddress = slot.endpoint.take (startDepth state slot.endpoint) := by
  rw [valid.start,valid.continuation,List.take_left]

theorem Slot.Valid.external {lower upper : Nat} {state : State} {reference : BST lower upper}
    {slot : Slot} (valid : slot.Valid state reference) :
    referenceAt reference.toRaw slot.endpoint = .empty := by
  rw [valid.continuation,referenceAt_append,valid.located]
  exact finish_external _ _

theorem Slot.Valid.within_height {lower upper : Nat} {state : State} {reference : BST lower upper}
    {slot : Slot} (valid : slot.Valid state reference) :
    startDepth state slot.endpoint +
      (PrimaryWings.exits (ComparatorPrimary.routing (restrict state slot.rootAddress) slot.primary)).length ≤
        reference.height := by
  rw [valid.start,← finish_length]
  exact (Nat.add_le_add_left (finish_height _ _) _).trans valid.height

abbrev Component := AuxiliaryComponent Nat Nat (Tagged Payload)
abbrev Family := Key → Component
abbrev Memory := Secondary.Row → Bool

def localMemory (memory : Memory) (endpoint : Key) (split : DepthSplit) : Bool :=
  memory ⟨split,endpoint.take split.lo⟩

/-- Initialization is pointwise and total; the clamp only handles addresses
outside the actual finite reference. Every actual slot has an unclamped
start, as `initialFamily_represents` proves. -/
def initialFamily {height : Nat} (secondary : DepthTree 0 height) (state : State)
    (memory : Memory) : Family := fun endpoint =>
  let start := min (startDepth state endpoint) height
  initializeMarked followsRight
    (suffixSource secondary (ComparatorStableSuffix.bits start (localMemory memory endpoint)) start
      ⟨Nat.zero_le _,Nat.min_le_right _ _⟩)

theorem initialFamily_represents {height : Nat} (secondary : DepthTree 0 height)
    (state : State) (memory : Memory) (endpoint : Key)
    (bound : startDepth state endpoint ≤ height) :
    Represents followsRight
      (suffixSource secondary
        (ComparatorStableSuffix.bits (startDepth state endpoint) (localMemory memory endpoint))
        (startDepth state endpoint) ⟨Nat.zero_le _,bound⟩)
      (initialFamily secondary state memory endpoint) := by
  simp only [initialFamily,Nat.min_eq_left bound]
  exact initialize_represents followsRight _ (suffixSource_raw _ _ _ _)

def projectedTree (state : State) (family : Family) (slot : Slot) : RawTree Nat :=
  ComparatorPrimary.projectedTree (restrict state slot.rootAddress) slot.primary
    (startDepth state slot.endpoint) (ComparatorRecords.erase (closed (family slot.endpoint)))

def projectedForest {lower upper : Nat} (state : State) (reference : BST lower upper)
    (family : Family) : List (RawTree Nat) :=
  (slots state reference).map (projectedTree state family)

theorem initialTree_inorder {lower upper : Nat} (state : State) (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (memory : Memory)
    {slot : Slot} (member : slot ∈ slots state reference) :
    (projectedTree state (initialFamily secondary state memory) slot).inorder =
      (slot.keys state).inorder := by
  have valid := slots_valid state reference slot member
  have bound : startDepth state slot.endpoint ≤ reference.height := by
    have within := valid.within_height
    omega
  exact ComparatorPrimary.stable_projected_inorder (restrict state slot.rootAddress) slot.primary
    secondary (startDepth state slot.endpoint) ⟨Nat.zero_le _,bound⟩ (localMemory memory slot.endpoint)
    (initialFamily secondary state memory slot.endpoint)
    (initialFamily_represents secondary state memory slot.endpoint bound) valid.within_height

/-- The initialized maintained sources project to the exact canonical
component domains. The comparison theorem pays its single linear forest
initialization allowance; no physical sentinel or depth key is introduced. -/
theorem initial_domains {lower upper : Nat} (state : State) (reference : BST lower upper)
    (secondary : DepthTree 0 reference.height) (memory : Memory) :
    CommonForest.domains (projectedForest state reference (initialFamily secondary state memory)) =
      CommonForest.domains (forest state reference.toRaw) := by
  rw [← slots_keys state reference]
  unfold CommonForest.domains projectedForest
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro slot member
  exact initialTree_inorder state reference secondary memory member

end MultiSplay.ComparatorForest
