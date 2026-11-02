import MultiSplay.GlobalPreferredHoles
import MultiSplay.ClassicalSwitchMarked

/-!
# A physical preferred-component representation

Every actual root component has the keys of the reference preferred path.
Its holes, in inorder, recursively represent the annotated off-path
reference subtrees. Thus the invariant records physical attachment, not
only a partition of keys into component domains.
-/

namespace MultiSplay.Global.Preferred

open DynamicOptimality (RawTree)
open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

variable {α : Type*}

/-- An actual tree with its recursively attached preferred components.
The equality of skeleton domains allows arbitrary auxiliary BST shapes. -/
inductive Realizes : State → RawTree α → RawTree α → Prop
  | empty (state : State) : Realizes state .empty .empty
  | component {state : State} {reference : RawTree α} (actual : MarkedTree α)
      (keys : actual.skeleton.inorder = (preferred state reference).inorder)
      (holes : ∀ (index : Nat) (entry : Key × RawTree α),
        (preferredHoles state reference)[index]? = some entry →
        Realizes (restrict state entry.1) entry.2 (actual.gapArray index)) :
      Realizes state reference actual.erase

/-- The local part of the invariant, retaining its actual marked shape. -/
def Component (state : State) (reference : RawTree α) (actual : MarkedTree α) : Prop :=
  actual.skeleton.inorder = (preferred state reference).inorder ∧
  ∀ (index : Nat) (entry : Key × RawTree α),
    (preferredHoles state reference)[index]? = some entry →
    Realizes (restrict state entry.1) entry.2 (actual.gapArray index)

theorem Component.realizes {state : State} {reference : RawTree α} {actual : MarkedTree α}
    (represented : Component state reference actual) : Realizes state reference actual.erase :=
  .component actual represented.1 represented.2

/-- Empty reference components are represented by an empty physical tree;
exposing them still provides their one empty inorder hole. -/
theorem Realizes.expose {state : State} {reference physical : RawTree α}
    (represented : Realizes state reference physical) :
    ∃ actual : MarkedTree α, actual.erase = physical ∧ Component state reference actual := by
  cases represented with
  | empty state =>
      refine ⟨.hole .empty, rfl, rfl, ?_⟩
      intro index entry found
      simp only [preferredHoles, List.getElem?_singleton] at found
      split at found
      · rename_i zero
        subst index
        cases Option.some.inj found
        exact .empty state
      · contradiction
  | component actual keys holes => exact ⟨actual, rfl, keys, holes⟩

theorem preferredHoles_size_le (state : State) (reference : RawTree α)
    {entry : Key × RawTree α} (member : entry ∈ preferredHoles state reference) :
    entry.2.size ≤ reference.size := by
  induction reference generalizing state entry with
  | empty => simp only [preferredHoles, List.mem_singleton] at member; subst entry; rfl
  | node left key right ihLeft ihRight =>
      cases side : state [] with
      | false =>
          simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte,
            List.mem_append, List.mem_singleton] at member
          rcases member with child | rfl
          · obtain ⟨entry, member, rfl⟩ := List.mem_map.mp child
            have bound := ihLeft (below state false) member
            simp only [Tree.size]
            omega
          · simp [Tree.size] <;> omega
      | true =>
          simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | child
          · simp [Tree.size] <;> omega
          · obtain ⟨entry, member, rfl⟩ := List.mem_map.mp child
            have bound := ihRight (below state true) member
            simp only [Tree.size]
            omega

theorem preferredHoles_size_lt (state : State) {reference : RawTree α}
    (nonempty : reference ≠ .empty) {entry : Key × RawTree α}
    (member : entry ∈ preferredHoles state reference) : entry.2.size < reference.size := by
  cases reference with
  | empty => exact False.elim (nonempty rfl)
  | node left key right =>
      cases side : state [] with
      | false =>
          simp only [preferredHoles, side, Bool.false_eq_true, ↓reduceIte,
            List.mem_append, List.mem_singleton] at member
          rcases member with child | rfl
          · obtain ⟨entry, member, rfl⟩ := List.mem_map.mp child
            have bound := preferredHoles_size_le (below state false) left member
            simp only [Tree.size]
            omega
          · simp [Tree.size] <;> omega
      | true =>
          simp only [preferredHoles, side, ↓reduceIte, List.mem_cons] at member
          rcases member with rfl | child
          · simp [Tree.size] <;> omega
          · obtain ⟨entry, member, rfl⟩ := List.mem_map.mp child
            have bound := preferredHoles_size_le (below state true) right member
            simp only [Tree.size]
            omega

/-- The canonical reference tree supplies an actual initial representation
for every preference state. No existence assumption on physical attachments
is needed. -/
theorem initial (state : State) (reference : RawTree α) : Realizes state reference reference := by
  cases reference with
  | empty => exact .empty state
  | node left key right =>
      have represented : Realizes state (.node left key right)
          (preferredMarked state (.node left key right)).erase := by
        refine .component (preferredMarked state (.node left key right)) (by simp) ?_
        intro index entry found
        have mapped := congrArg (Option.map Prod.snd) found
        have physicalFound : (preferredMarked state (.node left key right)).holes[index]? = some entry.2 := by
          simpa only [← List.getElem?_map, preferredHoles_trees, Option.map_some] using mapped
        have gap : (preferredMarked state (.node left key right)).gapArray index = entry.2 := by
          simp [MarkedTree.gapArray, physicalFound]
        rw [gap]
        exact initial (restrict state entry.1) entry.2
      simpa only [preferredMarked_erase] using represented
termination_by reference.size
decreasing_by
  exact preferredHoles_size_lt state (by simp) (List.mem_of_getElem? found)

/-- A local physical component exposes the incoming subtree in exactly
the gap consumed by the classical switch implementation. -/
theorem Component.incoming {state : State} {reference left right : RawTree α} {pivot : α}
    {address : Key} {spine : Spine α} (path : Path state reference address spine (.node left pivot right))
    {actual : MarkedTree α} (represented : Component state reference actual) :
    ∃ foreign : MarkedTree α,
      Component (restrict state (address ++ [!(state address)]))
        (if state address then left else right) foreign ∧
      foreign.erase = actual.gapArray (incomingGapIndex (state address) spine.lower
        (tail (restrict state address) (state address) (.node left pivot right))) := by
  have found := path.incoming_hole
  have child := represented.2 _ _ found
  obtain ⟨foreign, erase, child⟩ := child.expose
  refine ⟨foreign, child, ?_⟩
  exact erase

end MultiSplay.Global.Preferred
