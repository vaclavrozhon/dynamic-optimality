import MultiSplay.ClassicalSwitchHistory

/-! # Reference height bounds every classical component and prescribed join -/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree BST)
open ChaCha.MTR.Tree (inorder size length_inorder)
open ChaCha.Primary (Key)
open EndpointEncoding CommonForest

variable {α : Type*}

theorem forest_capacity {lower upper : Nat} (state : State) (reference : BST lower upper) :
    Capacity reference.height (forest state reference.toRaw) := by
  induction reference generalizing state with
  | empty => simp [Capacity, forest, preferred, otherComponents, DynamicOptimality.BST.toRaw,
      size, Splay.Tree.BST.height]
  | node left right ihl ihr =>
      intro tree member
      have rootBound := preferred_size_le_height state (.node left right)
      simp only [forest, List.mem_cons] at member
      rcases member with rfl | other
      · exact rootBound
      · have leftCapacity := ihl (below state false)
        have rightCapacity := ihr (below state true)
        simp only [DynamicOptimality.BST.toRaw, otherComponents, List.mem_cons, List.mem_append] at other
        rcases other with rfl | inLeft | inRight
        · cases side : state [] <;> simp only [side, Bool.false_eq_true, ↓reduceIte]
          · have bound := preferred_size_le_height (below state true) right
            simp only [Splay.Tree.BST.height]
            omega
          · have bound := preferred_size_le_height (below state false) left
            simp only [Splay.Tree.BST.height]
            omega
        · have bound := leftCapacity tree (by simp only [forest, List.mem_cons]; exact Or.inr inLeft)
          simp only [Splay.Tree.BST.height]
          omega
        · have bound := rightCapacity tree (by simp only [forest, List.mem_cons]; exact Or.inr inRight)
          simp only [Splay.Tree.BST.height]
          omega

theorem leftWord_joinFits (lower upper : Boundary α) (old incoming : List α) (pivot : α)
    {bound : Nat} (fits : (lower.lowerKeys ++ [pivot] ++ incoming ++ upper.upperKeys).length ≤ bound) :
    ∀ event ∈ leftWord lower upper old incoming pivot, Domains.JoinFits bound event := by
  cases lower <;> cases upper <;>
    simp_all [leftWord, leftToRightWord, noLowerWord, noUpperWord, noGuardsWord,
      Domains.JoinFits, Boundary.lowerKeys, Boundary.upperKeys] <;> omega

theorem joinFits_mirror (bound : Nat) (event : Event α) :
    Domains.JoinFits bound event.mirror ↔ Domains.JoinFits bound event := by
  cases event <;> simp [Event.mirror, Domains.JoinFits] <;> omega

theorem word_joinFits (oldSide : Bool) (lower upper : Boundary α) (old incoming : List α) (pivot : α)
    {bound : Nat} (fits : (afterKeys oldSide lower upper incoming pivot).length ≤ bound) :
    ∀ event ∈ word oldSide lower upper old incoming pivot, Domains.JoinFits bound event := by
  cases oldSide with
  | false =>
      simpa [word] using leftWord_joinFits lower upper old incoming pivot
        (by simpa [afterKeys, beforeKeys, List.append_assoc] using fits)
  | true =>
      have reflected : (upper.reflect.lowerKeys ++ [pivot] ++ incoming.reverse ++ lower.reflect.upperKeys).length ≤ bound := by
        simpa [afterKeys, beforeKeys, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using fits
      intro event member
      obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
      exact (joinFits_mirror bound source).mpr
        (leftWord_joinFits upper.reflect lower.reflect old.reverse incoming.reverse pivot reflected source present)

theorem eventWord_joinFits {lower upper : Nat} (reference : BST lower upper) (state : State) (address : Key)
    (real : referenceAt reference.toRaw address ≠ .empty) :
    ∀ event ∈ eventWord reference.toRaw state address, Domains.JoinFits reference.height event := by
  obtain ⟨remainder,_,after⟩ := selected_partition state reference.toRaw address real
  have bound := forest_capacity (toggle state address) reference (targetComponent state reference.toRaw address)
    (after.mem_iff.mpr (by simp))
  have path := selected_path state address real
  cases focus : referenceAt reference.toRaw address with
  | empty => exact False.elim (real focus)
  | node left pivot right =>
      rw [focus] at path
      have targetEq := congrArg inorder path.after
      have side : restrict state (address.take (startDepth state address))
          (address.drop (startDepth state address)) = state address := by
        rw [restrict_eq, List.take_append_drop]
      have current : restrict (restrict state (address.take (startDepth state address)))
          (address.drop (startDepth state address)) = restrict state address := by
        rw [← restrict_append, List.take_append_drop]
      rw [Spine.before_inorder, side, current] at targetEq
      have fits : (afterKeys (state address) (componentSpine state reference.toRaw address).lower
          (componentSpine state reference.toRaw address).upper
          (inorder (tail (restrict state address) (!(state address)) (.node left pivot right))) pivot).length ≤ reference.height := by
        rw [afterKeys, ← targetEq, length_inorder]
        exact bound
      simpa only [eventWord, focus] using word_joinFits (state address)
        (componentSpine state reference.toRaw address).lower (componentSpine state reference.toRaw address).upper
        (inorder (tail (restrict state address) (state address) (.node left pivot right)))
        (inorder (tail (restrict state address) (!(state address)) (.node left pivot right))) pivot fits

theorem schedule_joinFits {lower upper : Nat} (reference : BST lower upper) (state : State) (owners : List Key)
    (real : ∀ owner ∈ owners, referenceAt reference.toRaw owner ≠ .empty) :
    ∀ event ∈ (schedule state owners).flatMap
      (fun entry => eventWord reference.toRaw entry.1 entry.2), Domains.JoinFits reference.height event := by
  induction owners generalizing state with
  | nil => simp [schedule]
  | cons owner rest ih =>
      intro event member
      simp only [schedule, List.flatMap_cons, List.mem_append] at member
      rcases member with head | tail
      · exact eventWord_joinFits reference state owner (real owner (by simp)) event head
      · exact ih (toggle state owner) (fun next inRest => real next (by simp [inRest])) event tail

theorem request_joinFits {lower upper : Nat} (reference : BST lower upper) (state : State) (address : Key)
    (real : referenceAt reference.toRaw address ≠ .empty) :
    ∀ event ∈ requestWord reference.toRaw state address, Domains.JoinFits reference.height event := by
  apply schedule_joinFits reference state _
  intro owner member
  exact referenceAt_prefix_nonempty real
    (ascendingEmissions_prefix ((actualEmissions_perm state address).mem_iff.mp member))

theorem history_joinFits {lower upper : Nat} (reference : BST lower upper) (state : State) (addresses : List Key)
    (real : ∀ address ∈ addresses, referenceAt reference.toRaw address ≠ .empty) :
    ∀ event ∈ historyWord reference.toRaw state addresses, Domains.JoinFits reference.height event := by
  induction addresses generalizing state with
  | nil => simp [historyWord]
  | cons address rest ih =>
      intro event member
      simp only [historyWord, List.mem_append] at member
      rcases member with head | tail
      · exact request_joinFits reference state address (real address (by simp)) event head
      · exact ih (nodeStep state address) (fun next inRest => real next (by simp [inRest])) event tail

end MultiSplay.ClassicalSwitch
