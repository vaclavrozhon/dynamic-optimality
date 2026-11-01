import MultiSplay.ComparatorForestEndpoints

/-! # The literal component slots exchanged by a root-component switch -/

namespace MultiSplay.ComparatorForest

open DynamicOptimality (RawTree BST)
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

/-- The main component retains its indexed primary subtree and acquires
the incoming endpoint. The parked component retains the old endpoint. -/
structure Pair (state : State) (address : Key) (source incoming target parked : Slot) : Prop where
  target_eq : target = { source with endpoint := incoming.endpoint }
  parked_endpoint : parked.endpoint = source.endpoint
  incoming_root : incoming.rootAddress = address ++ [!(state address)]
  parked_root : parked.rootAddress = address ++ [state address]
  source_prefix : source.rootAddress.IsPrefix address

theorem Pair.lift {state : State} {edge : Bool} {address : Key}
    {source incoming target parked : Slot}
    (pair : Pair (below state edge) address source incoming target parked) :
    Pair state (edge::address) (source.lift edge) (incoming.lift edge)
      (target.lift edge) (parked.lift edge) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [pair.target_eq]
    rfl
  · exact congrArg (List.cons edge) pair.parked_endpoint
  · simpa only [Slot.lift,List.cons_append,below] using congrArg (List.cons edge) pair.incoming_root
  · simpa only [Slot.lift,List.cons_append,below] using congrArg (List.cons edge) pair.parked_root
  · simpa [Slot.lift] using pair.source_prefix

theorem move_first {α : Type*} {before after : List α} {selected : α}
    (run : before.Perm (selected::after)) (front back : List α) :
    (front ++ before ++ back).Perm (selected :: (front ++ after ++ back)) := by
  have moved := (run.append_left front).append_right back
  exact moved.trans (by simpa only [List.append_assoc,List.cons_append] using
    (List.perm_middle (a := selected) (l₁ := front) (l₂ := after ++ back)))

theorem move_pair {α : Type*} {before after : List α} {first second : α}
    (run : before.Perm (first::second::after)) (front back : List α) :
    (front ++ before ++ back).Perm (first::second::(front ++ after ++ back)) := by
  have moved := (run.append_left front).append_right back
  have swapped := (List.perm_append_comm (l₁ := front) (l₂ := [first,second])).append_right (after++back)
  exact moved.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using swapped)

theorem root_other_partition {lower upper : Nat} (state : State) (reference : BST lower upper)
    (address : Key) (follows : RootPreferred state address)
    (real : referenceAt reference.toRaw address ≠ .empty) :
    ∃ incoming parked remainder,
      (otherSlots state reference).Perm (incoming::remainder) ∧
      (otherSlots (toggle state address) reference).Perm (parked::remainder) ∧
      incoming.rootAddress = address ++ [!(state address)] ∧
      parked.rootAddress = address ++ [state address] ∧
      (rootSlot (toggle state address) reference).endpoint = incoming.endpoint ∧
      parked.endpoint = (rootSlot state reference).endpoint := by
  induction reference generalizing state address with
  | empty => exact False.elim (real (referenceAt_empty _))
  | @node lower key upper left right ihl ihr =>
      cases address with
      | nil =>
          let remainder := (otherSlots (below state false) left).map (Slot.lift false) ++
            (otherSlots (below state true) right).map (Slot.lift true)
          cases side : state [] with
          | false =>
              refine ⟨(rootSlot (below state true) right).lift true,
                (rootSlot (below state false) left).lift false,remainder,?_,?_,?_,?_,?_,?_⟩ <;>
                simp [otherSlots,rootSlot,Slot.lift,finish,DynamicOptimality.BST.toRaw,side,
                  toggle,below_toggle_empty,remainder]
          | true =>
              refine ⟨(rootSlot (below state false) left).lift false,
                (rootSlot (below state true) right).lift true,remainder,?_,?_,?_,?_,?_,?_⟩ <;>
                simp [otherSlots,rootSlot,Slot.lift,finish,DynamicOptimality.BST.toRaw,side,
                  toggle,below_toggle_empty,remainder]
      | cons edge address =>
          obtain ⟨agrees,childFollows⟩ := (rootPreferred_cons _ _ _).mp follows
          cases edge with
          | false =>
              obtain ⟨incoming,parked,remainder,before,after,incomingRoot,parkedRoot,incomingEnd,parkedEnd⟩ :=
                ihl (below state false) address childFollows real
              have sibling := below_toggle_other state false true address (by decide)
              have root : toggle state (false::address) [] = false := by simp [toggle,agrees]
              refine ⟨incoming.lift false,parked.lift false,
                (rootSlot (below state true) right).lift true ::
                  (remainder.map (Slot.lift false) ++ (otherSlots (below state true) right).map (Slot.lift true)),
                ?_,?_,?_,?_,?_,?_⟩
              · simpa only [otherSlots,agrees,Bool.false_eq_true,if_false,List.map_cons,List.cons_append,
                  List.nil_append] using
                  move_first (before.map (Slot.lift false)) [(rootSlot (below state true) right).lift true]
                    ((otherSlots (below state true) right).map (Slot.lift true))
              · simpa only [otherSlots,root,Bool.false_eq_true,if_false,below_toggle_cons,sibling,
                  List.map_cons,List.cons_append,List.nil_append] using
                  move_first (after.map (Slot.lift false)) [(rootSlot (below state true) right).lift true]
                    ((otherSlots (below state true) right).map (Slot.lift true))
              · simpa only [Slot.lift,List.cons_append,below] using congrArg (List.cons false) incomingRoot
              · simpa only [Slot.lift,List.cons_append,below] using congrArg (List.cons false) parkedRoot
              · simpa only [rootSlot,finish,DynamicOptimality.BST.toRaw,root,Bool.false_eq_true,if_false,
                  below_toggle_cons,Slot.lift] using congrArg (List.cons false) incomingEnd
              · simpa only [rootSlot,finish,DynamicOptimality.BST.toRaw,agrees,Bool.false_eq_true,if_false,
                  Slot.lift] using congrArg (List.cons false) parkedEnd
          | true =>
              obtain ⟨incoming,parked,remainder,before,after,incomingRoot,parkedRoot,incomingEnd,parkedEnd⟩ :=
                ihr (below state true) address childFollows real
              have sibling := below_toggle_other state true false address (by decide)
              have root : toggle state (true::address) [] = true := by simp [toggle,agrees]
              refine ⟨incoming.lift true,parked.lift true,
                (rootSlot (below state false) left).lift false ::
                  ((otherSlots (below state false) left).map (Slot.lift false) ++ remainder.map (Slot.lift true)),
                ?_,?_,?_,?_,?_,?_⟩
              · simpa only [otherSlots,agrees,if_true,List.map_cons,List.cons_append,List.nil_append,
                  List.append_nil] using
                  move_first (before.map (Slot.lift true))
                    ((rootSlot (below state false) left).lift false :: (otherSlots (below state false) left).map (Slot.lift false)) []
              · simpa only [otherSlots,root,if_true,below_toggle_cons,sibling,List.map_cons,List.cons_append,
                  List.nil_append,List.append_nil] using
                  move_first (after.map (Slot.lift true))
                    ((rootSlot (below state false) left).lift false :: (otherSlots (below state false) left).map (Slot.lift false)) []
              · simpa only [Slot.lift,List.cons_append,below] using congrArg (List.cons true) incomingRoot
              · simpa only [Slot.lift,List.cons_append,below] using congrArg (List.cons true) parkedRoot
              · simpa only [rootSlot,finish,DynamicOptimality.BST.toRaw,root,if_true,below_toggle_cons,Slot.lift]
                  using congrArg (List.cons true) incomingEnd
              · simpa only [rootSlot,finish,DynamicOptimality.BST.toRaw,agrees,if_true,Slot.lift]
                  using congrArg (List.cons true) parkedEnd

theorem root_partition {lower upper : Nat} (state : State) (reference : BST lower upper)
    (address : Key) (follows : RootPreferred state address)
    (real : referenceAt reference.toRaw address ≠ .empty) :
    ∃ incoming parked remainder,
      (slots state reference).Perm (rootSlot state reference :: incoming :: remainder) ∧
      (slots (toggle state address) reference).Perm
        (rootSlot (toggle state address) reference :: parked :: remainder) ∧
      Pair state address (rootSlot state reference) incoming
        (rootSlot (toggle state address) reference) parked := by
  obtain ⟨incoming,parked,remainder,before,after,incomingRoot,parkedRoot,incomingEnd,parkedEnd⟩ :=
    root_other_partition state reference address follows real
  refine ⟨incoming,parked,remainder,before.cons _,after.cons _,?_,parkedEnd,incomingRoot,parkedRoot,?_⟩
  · change rootSlot (toggle state address) reference =
      ⟨_,_,reference,[],incoming.endpoint⟩
    unfold rootSlot
    exact congrArg (fun endpoint => Slot.mk _ _ reference [] endpoint) incomingEnd
  · exact List.nil_prefix

end MultiSplay.ComparatorForest
