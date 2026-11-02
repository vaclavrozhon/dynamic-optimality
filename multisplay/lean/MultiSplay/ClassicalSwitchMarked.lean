import MultiSplay.ClassicalSwitchSelected

/-!
# Ordered opaque subtrees of a canonical preferred component

The marks retain exactly the preferred reference path. Each hole contains an
actual off-path reference subtree, including empty subtrees. Its annotation is
its relative reference address, so its preference state is obtained by
`restrict`, without a separate address table or a runtime finger.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder size)
open ChaCha.MTR.Pointer (MarkedTree)
open ChaCha.Primary (Key)
open EndpointEncoding

variable {α : Type*}

def preferredMarked : State → RawTree α → MarkedTree α
  | _, .empty => .hole .empty
  | state, .node left key right =>
      if state [] then .node (.hole left) key (preferredMarked (below state true) right)
      else .node (preferredMarked (below state false) left) key (.hole right)

@[simp] theorem preferredMarked_skeleton (state : State) (reference : RawTree α) :
    (preferredMarked state reference).skeleton = preferred state reference := by
  induction reference generalizing state with
  | empty => rfl
  | node left key right ihl ihr =>
      cases side : state [] <;> simp [preferredMarked, preferred, side, MarkedTree.skeleton, ihl, ihr]

@[simp] theorem preferredMarked_erase (state : State) (reference : RawTree α) :
    (preferredMarked state reference).erase = reference := by
  induction reference generalizing state with
  | empty => rfl
  | node left key right ihl ihr =>
      cases side : state [] <;> simp [preferredMarked, side, MarkedTree.erase, ihl, ihr]

def prefixHoles (address : Key) (holes : List (Key × RawTree α)) : List (Key × RawTree α) :=
  holes.map fun entry => (address ++ entry.1, entry.2)

@[simp] theorem prefixHoles_nil (holes : List (Key × RawTree α)) : prefixHoles [] holes = holes := by
  simp [prefixHoles]

@[simp] theorem prefixHoles_length (address : Key) (holes : List (Key × RawTree α)) :
    (prefixHoles address holes).length = holes.length := by simp [prefixHoles]

theorem prefixHoles_append (address : Key) (first rest : List (Key × RawTree α)) :
    prefixHoles address (first ++ rest) = prefixHoles address first ++ prefixHoles address rest := by
  simp [prefixHoles]

theorem prefixHoles_comp (first rest : Key) (holes : List (Key × RawTree α)) :
    prefixHoles first (prefixHoles rest holes) = prefixHoles (first ++ rest) holes := by
  simp [prefixHoles, List.map_map, Function.comp_def, List.append_assoc]

def preferredHoles : State → RawTree α → List (Key × RawTree α)
  | _, .empty => [([], .empty)]
  | state, .node left _ right =>
      if state [] then ([false], left) :: prefixHoles [true] (preferredHoles (below state true) right)
      else prefixHoles [false] (preferredHoles (below state false) left) ++ [([true], right)]

@[simp] theorem preferredHoles_trees (state : State) (reference : RawTree α) :
    (preferredHoles state reference).map Prod.snd = (preferredMarked state reference).holes := by
  induction reference generalizing state with
  | empty => rfl
  | node left key right ihl ihr =>
      cases side : state [] <;>
        simp [preferredHoles, preferredMarked, side, MarkedTree.holes, prefixHoles,
          List.map_map, Function.comp_def, ihl, ihr]

theorem preferredHoles_length (state : State) (reference : RawTree α) :
    (preferredHoles state reference).length = size (preferred state reference) + 1 := by
  have length := congrArg List.length (preferredHoles_trees state reference)
  simpa only [List.length_map, MarkedTree.holes_length, preferredMarked_skeleton] using length

/-- Every annotation names the actual subtree stored in that hole. -/
theorem preferredHoles_referenceAt (state : State) (reference : RawTree α)
    {entry : Key × RawTree α} (member : entry ∈ preferredHoles state reference) :
    referenceAt reference entry.1 = entry.2 := by
  induction reference generalizing state entry with
  | empty => simp only [preferredHoles, List.mem_singleton] at member; subst entry; rfl
  | node left key right ihl ihr =>
      cases side : state [] with
      | false =>
          simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte, List.mem_append,
            List.mem_singleton] at member
          rcases member with previous | rfl
          · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
            exact ihl (below state false) present
          · rfl
      | true =>
          simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | previous
          · rfl
          · obtain ⟨child,present,rfl⟩ := List.mem_map.mp previous
            exact ihr (below state true) present

theorem Spine.lowerKeys_append (inside outside : Spine α) :
    (inside ++ outside).lowerKeys = outside.lowerKeys ++ inside.lowerKeys := by
  induction inside with
  | nil => simp [Spine.lowerKeys]
  | cons entry rest ih =>
      rcases entry with ⟨side,key⟩
      cases side <;> simp [Spine.lowerKeys, ih, List.append_assoc]

/-- The holes below a preferred-path node form a contiguous ordered interval.
Its first gap is determined by the lower reference ancestors. -/
theorem Path.holes_interval {state : State} {reference focus : RawTree α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine focus) :
    ∃ front back,
      preferredHoles state reference = front ++ prefixHoles address
        (preferredHoles (restrict state address) focus) ++ back ∧
      front.length = spine.lowerKeys.length := by
  induction path with
  | here state reference => exact ⟨[],[],by simp [restrict],rfl⟩
  | @left state left right focus key address spine agrees rest ih =>
      obtain ⟨front,back,holes,length⟩ := ih
      refine ⟨prefixHoles [false] front, prefixHoles [false] back ++ [([true],right)],?_,?_⟩
      · simp [preferredHoles, agrees, holes, prefixHoles_append, prefixHoles_comp,
          restrict, List.append_assoc]
      · simp [length, Spine.lowerKeys_append, Spine.lowerKeys]
  | @right state left right focus key address spine agrees rest ih =>
      obtain ⟨front,back,holes,length⟩ := ih
      refine ⟨([false],left)::prefixHoles [true] front, prefixHoles [true] back,?_,?_⟩
      · simp [preferredHoles, agrees, holes, prefixHoles_append, prefixHoles_comp,
          restrict, List.append_assoc]
      · simp [length, Spine.lowerKeys_append, Spine.lowerKeys]

theorem preferredHoles_incoming (state : State) (left right : RawTree α) (pivot : α) :
    (preferredHoles state (.node left pivot right))[
      if state [] then 0 else size (preferred (below state false) left) + 1]? =
      some ([!(state [])], if state [] then left else right) := by
  cases side : state [] with
  | false =>
      have length := preferredHoles_length (below state false) left
      simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [← length, ← prefixHoles_length [false] (preferredHoles (below state false) left)]
      simp
  | true => simp [preferredHoles, side]

/-- The incoming component is exactly the pivot-adjacent gap, with its actual
relative address and actual reference subtree. -/
theorem Path.incoming_hole {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right)) :
    (preferredHoles state reference)[spine.lower.lowerKeys.length +
      (if state address then 0 else size (tail (restrict state address) (state address) (.node left pivot right)) + 1)]? =
      some (address ++ [!(state address)], if state address then left else right) := by
  obtain ⟨front,back,holes,length⟩ := path.holes_interval
  have side : restrict state address [] = state address := by simp [restrict_eq]
  have localHole := preferredHoles_incoming (restrict state address) left right pivot
  rw [side] at localHole
  have index : (if state address then 0 else size (preferred (EndpointEncoding.below (restrict state address) false) left) + 1) =
      (if state address then 0 else size (tail (restrict state address) (state address) (.node left pivot right)) + 1) := by
    cases direction : state address <;> simp [direction, tail]
  rw [index] at localHole
  rw [holes, List.append_assoc, Spine.lower_domain, ← length,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp localHole).1)]
  have mapped := congrArg (Option.map fun entry : Key × RawTree α => (address ++ entry.1,entry.2)) localHole
  simpa [prefixHoles, List.getElem?_map] using mapped

end MultiSplay.ClassicalSwitch
