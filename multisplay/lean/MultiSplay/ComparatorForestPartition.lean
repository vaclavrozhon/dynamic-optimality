import MultiSplay.ComparatorForestRootPartition

/-! # Exactly two endpoint-indexed slots change at a classical switch -/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open ChaCha.Primary (Key)
open EndpointEncoding ClassicalSwitch

theorem finish_toggle_nonroot (state : State) (reference : RawTree Nat) (address : Key)
    (outside : ¬ RootPreferred state address) :
    finish (toggle state address) reference = finish state reference := by
  induction address generalizing state reference with
  | nil => exact False.elim (outside (rootPreferred_nil _))
  | cons edge address ih =>
      cases reference with
      | empty => rfl
      | node left pivot right =>
          have root : toggle state (edge::address) [] = state [] := by simp [toggle]
          by_cases agrees : state [] = edge
          · have childOutside : ¬ RootPreferred (below state edge) address := by
              intro child
              exact outside ((rootPreferred_cons _ _ _).mpr ⟨agrees,child⟩)
            cases edge with
            | false =>
                simp only [finish,root,agrees,Bool.false_eq_true,if_false,below_toggle_cons,ih _ _ childOutside]
            | true =>
                simp only [finish,root,agrees,if_true,below_toggle_cons,ih _ _ childOutside]
          · cases edge <;> cases side : state [] <;> simp_all only [Bool.true_eq_false,Bool.false_eq_true,
              not_true_eq_false,not_false_eq_true]
            · simp only [finish,root,side,if_true,below_toggle_other state false true address (by decide)]
            · simp only [finish,root,side,Bool.false_eq_true,if_false,
                below_toggle_other state true false address (by decide)]

theorem rootSlot_toggle_nonroot {lower upper : Nat} (state : State)
    (reference : BST lower upper) (address : Key) (outside : ¬ RootPreferred state address) :
    rootSlot (toggle state address) reference = rootSlot state reference := by
  simp only [rootSlot,finish_toggle_nonroot state reference.toRaw address outside]

private theorem add_root {lower upper : Nat} {state : State} {reference : BST lower upper}
    {address : Key} {source incoming target parked : Slot} {remainder : List Slot}
    (outside : ¬ RootPreferred state address)
    (before : (otherSlots state reference).Perm (source::incoming::remainder))
    (after : (otherSlots (toggle state address) reference).Perm (target::parked::remainder)) :
    (slots state reference).Perm (source::incoming::rootSlot state reference::remainder) ∧
    (slots (toggle state address) reference).Perm (target::parked::rootSlot state reference::remainder) := by
  constructor
  · simpa only [slots,List.cons_append,List.nil_append,List.append_nil] using
      move_pair before [rootSlot state reference] []
  · simpa only [slots,rootSlot_toggle_nonroot state reference address outside,List.cons_append,
      List.nil_append,List.append_nil] using
      move_pair after [rootSlot state reference] []

theorem nonroot_partition {lower upper : Nat} (state : State) (reference : BST lower upper)
    (address : Key) (outside : ¬ RootPreferred state address)
    (real : referenceAt reference.toRaw address ≠ .empty) :
    ∃ source incoming target parked remainder,
      (otherSlots state reference).Perm (source::incoming::remainder) ∧
      (otherSlots (toggle state address) reference).Perm (target::parked::remainder) ∧
      Pair state address source incoming target parked := by
  induction reference generalizing state address with
  | empty => exact False.elim (real (referenceAt_empty _))
  | @node lower pivot upper left right ihl ihr =>
      cases address with
      | nil => exact False.elim (outside (rootPreferred_nil _))
      | cons edge address =>
          have root : toggle state (edge::address) [] = state [] := by simp [toggle]
          cases edge with
          | false =>
              have sibling := below_toggle_other state false true address (by decide)
              cases side : state [] with
              | false =>
                  have childOutside : ¬ RootPreferred (below state false) address := by
                    intro child
                    exact outside ((rootPreferred_cons _ _ _).mpr ⟨side,child⟩)
                  obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ :=
                    ihl (below state false) address childOutside real
                  refine ⟨source.lift false,incoming.lift false,target.lift false,parked.lift false,
                    (rootSlot (below state true) right).lift true ::
                      (remainder.map (Slot.lift false) ++ (otherSlots (below state true) right).map (Slot.lift true)),
                    ?_,?_,pair.lift⟩
                  · simpa only [otherSlots,side,Bool.false_eq_true,if_false,List.map_cons,List.cons_append,List.nil_append] using
                      move_pair (before.map (Slot.lift false)) [(rootSlot (below state true) right).lift true]
                        ((otherSlots (below state true) right).map (Slot.lift true))
                  · simpa only [otherSlots,root,side,Bool.false_eq_true,if_false,below_toggle_cons,sibling,
                      List.map_cons,List.cons_append,List.nil_append] using
                      move_pair (after.map (Slot.lift false)) [(rootSlot (below state true) right).lift true]
                        ((otherSlots (below state true) right).map (Slot.lift true))
              | true =>
                  have selected : ∃ source incoming target parked remainder,
                      (slots (below state false) left).Perm (source::incoming::remainder) ∧
                      (slots (toggle (below state false) address) left).Perm (target::parked::remainder) ∧
                      Pair (below state false) address source incoming target parked := by
                    by_cases childFollows : RootPreferred (below state false) address
                    · obtain ⟨incoming,parked,remainder,before,after,pair⟩ :=
                        root_partition (below state false) left address childFollows real
                      exact ⟨_,incoming,_,parked,remainder,before,after,pair⟩
                    · obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ :=
                        ihl (below state false) address childFollows real
                      have framed := add_root childFollows before after
                      exact ⟨source,incoming,target,parked,_,framed.1,framed.2,pair⟩
                  obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ := selected
                  refine ⟨source.lift false,incoming.lift false,target.lift false,parked.lift false,
                    remainder.map (Slot.lift false) ++ (otherSlots (below state true) right).map (Slot.lift true),
                    ?_,?_,pair.lift⟩
                  · simpa only [otherSlots,slots,side,if_true,List.map_cons,List.cons_append,List.nil_append] using
                      move_pair (before.map (Slot.lift false)) [] ((otherSlots (below state true) right).map (Slot.lift true))
                  · simpa only [otherSlots,slots,root,side,if_true,below_toggle_cons,sibling,List.map_cons,
                      List.cons_append,List.nil_append] using
                      move_pair (after.map (Slot.lift false)) [] ((otherSlots (below state true) right).map (Slot.lift true))
          | true =>
              have sibling := below_toggle_other state true false address (by decide)
              cases side : state [] with
              | true =>
                  have childOutside : ¬ RootPreferred (below state true) address := by
                    intro child
                    exact outside ((rootPreferred_cons _ _ _).mpr ⟨side,child⟩)
                  obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ :=
                    ihr (below state true) address childOutside real
                  refine ⟨source.lift true,incoming.lift true,target.lift true,parked.lift true,
                    (rootSlot (below state false) left).lift false ::
                      ((otherSlots (below state false) left).map (Slot.lift false) ++ remainder.map (Slot.lift true)),
                    ?_,?_,pair.lift⟩
                  · simpa only [otherSlots,side,if_true,List.map_cons,List.cons_append,List.nil_append,List.append_nil] using
                      move_pair (before.map (Slot.lift true))
                        ((rootSlot (below state false) left).lift false :: (otherSlots (below state false) left).map (Slot.lift false)) []
                  · simpa only [otherSlots,root,side,if_true,below_toggle_cons,sibling,List.map_cons,
                      List.cons_append,List.nil_append,List.append_nil] using
                      move_pair (after.map (Slot.lift true))
                        ((rootSlot (below state false) left).lift false :: (otherSlots (below state false) left).map (Slot.lift false)) []
              | false =>
                  have selected : ∃ source incoming target parked remainder,
                      (slots (below state true) right).Perm (source::incoming::remainder) ∧
                      (slots (toggle (below state true) address) right).Perm (target::parked::remainder) ∧
                      Pair (below state true) address source incoming target parked := by
                    by_cases childFollows : RootPreferred (below state true) address
                    · obtain ⟨incoming,parked,remainder,before,after,pair⟩ :=
                        root_partition (below state true) right address childFollows real
                      exact ⟨_,incoming,_,parked,remainder,before,after,pair⟩
                    · obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ :=
                        ihr (below state true) address childFollows real
                      have framed := add_root childFollows before after
                      exact ⟨source,incoming,target,parked,_,framed.1,framed.2,pair⟩
                  obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ := selected
                  have shuffleBefore := List.Perm.cons ((rootSlot (below state true) right).lift true)
                    (List.perm_append_comm (l₁ := (otherSlots (below state false) left).map (Slot.lift false))
                      (l₂ := (otherSlots (below state true) right).map (Slot.lift true)))
                  have shuffleAfter := List.Perm.cons ((rootSlot (toggle (below state true) address) right).lift true)
                    (List.perm_append_comm (l₁ := (otherSlots (below state false) left).map (Slot.lift false))
                      (l₂ := (otherSlots (toggle (below state true) address) right).map (Slot.lift true)))
                  refine ⟨source.lift true,incoming.lift true,target.lift true,parked.lift true,
                    remainder.map (Slot.lift true) ++ (otherSlots (below state false) left).map (Slot.lift false),
                    ?_,?_,pair.lift⟩
                  · simpa only [otherSlots,side,Bool.false_eq_true,if_false] using shuffleBefore.trans (by
                      simpa only [slots,List.map_cons,List.cons_append,List.nil_append] using
                        move_pair (before.map (Slot.lift true)) [] ((otherSlots (below state false) left).map (Slot.lift false)))
                  · simpa only [otherSlots,root,side,Bool.false_eq_true,if_false,below_toggle_cons,sibling] using
                      shuffleAfter.trans (by
                        simpa only [slots,List.map_cons,List.cons_append,List.nil_append] using
                          move_pair (after.map (Slot.lift true)) [] ((otherSlots (below state false) left).map (Slot.lift false)))

/-- One classical switch changes exactly its selected and incoming slots.
Every remaining indexed subtree, root address and endpoint is literally
retained, including components above the selected component. -/
theorem selected_partition {lower upper : Nat} (state : State) (reference : BST lower upper)
    (address : Key) (real : referenceAt reference.toRaw address ≠ .empty) :
    ∃ source incoming target parked remainder,
      (slots state reference).Perm (source::incoming::remainder) ∧
      (slots (toggle state address) reference).Perm (target::parked::remainder) ∧
      Pair state address source incoming target parked := by
  by_cases follows : RootPreferred state address
  · obtain ⟨incoming,parked,remainder,before,after,pair⟩ := root_partition state reference address follows real
    exact ⟨_,incoming,_,parked,remainder,before,after,pair⟩
  · obtain ⟨source,incoming,target,parked,remainder,before,after,pair⟩ :=
      nonroot_partition state reference address follows real
    have framed := add_root follows before after
    exact ⟨source,incoming,target,parked,_,framed.1,framed.2,pair⟩

end MultiSplay.ComparatorForest
