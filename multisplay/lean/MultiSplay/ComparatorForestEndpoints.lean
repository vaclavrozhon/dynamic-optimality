import MultiSplay.ComparatorForestInitialization

/-! # Each external endpoint indexes exactly one preferred component -/

namespace MultiSplay.ComparatorForest

open DynamicOptimality
open TangoSquared.Primary (Key)
open EndpointEncoding ClassicalSwitch

def externalAddresses : RawTree Nat → List Key
  | .empty => [[]]
  | .node left _ right =>
      (externalAddresses left).map (List.cons false) ++
        (externalAddresses right).map (List.cons true)

theorem externalAddresses_nodup (reference : RawTree Nat) : (externalAddresses reference).Nodup := by
  induction reference with
  | empty => simp [externalAddresses]
  | node left key right ihl ihr =>
      rw [externalAddresses,List.nodup_append]
      refine ⟨ihl.map (fun _ _ equal => List.cons_injective equal),
        ihr.map (fun _ _ equal => List.cons_injective equal),?_⟩
      intro first inLeft second inRight same
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp inLeft
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp inRight
      cases same

private theorem interleave (first second : Key) (left right : List Key) :
    (first::second::(left++right)).Perm ((first::left)++(second::right)) := by
  exact (List.perm_middle (a := second) (l₁ := left) (l₂ := right)).symm.cons first

theorem slots_endpoints {lower upper : Nat} (state : State) (reference : BST lower upper) :
    ((slots state reference).map Slot.endpoint).Perm (externalAddresses reference.toRaw) := by
  induction reference generalizing state with
  | empty => exact List.Perm.refl _
  | @node lower key upper left right ihl ihr =>
      have leftRun := (ihl (below state false)).map (List.cons false)
      have rightRun := (ihr (below state true)).map (List.cons true)
      have combined := leftRun.append rightRun
      simp only [slots,List.map_cons,List.map_map,Function.comp_def] at combined
      cases side : state [] with
      | false =>
          have reordered := interleave
            (false::finish (below state false) (BST.toRaw left))
            (true::finish (below state true) (BST.toRaw right))
            ((otherSlots (below state false) left).map fun slot => false::slot.endpoint)
            ((otherSlots (below state true) right).map fun slot => true::slot.endpoint)
          simpa only [slots,otherSlots,rootSlot,Slot.lift,List.map_cons,List.map_append,List.map_map,
            Function.comp_def,side,Bool.false_eq_true,if_false,DynamicOptimality.BST.toRaw,
            finish,externalAddresses] using reordered.trans combined
      | true =>
          have reordered := (List.perm_middle
            (a := true::finish (below state true) (BST.toRaw right))
            (l₁ := (false::finish (below state false) (BST.toRaw left)) ::
              ((otherSlots (below state false) left).map fun slot => false::slot.endpoint))
            (l₂ := (otherSlots (below state true) right).map fun slot => true::slot.endpoint)).symm
          simpa only [slots,otherSlots,rootSlot,Slot.lift,List.map_cons,List.map_append,List.map_map,
            Function.comp_def,side,if_true,DynamicOptimality.BST.toRaw,finish,externalAddresses,
            List.cons_append] using reordered.trans combined

theorem slots_endpoints_nodup {lower upper : Nat} (state : State) (reference : BST lower upper) :
    ((slots state reference).map Slot.endpoint).Nodup :=
  (slots_endpoints state reference).symm.nodup (externalAddresses_nodup _)

theorem slots_nodup {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (slots state reference).Nodup :=
  (slots_endpoints_nodup state reference).of_map _

theorem slots_roots_nodup {lower upper : Nat} (state : State) (reference : BST lower upper) :
    ((slots state reference).map Slot.rootAddress).Nodup := by
  apply (slots_nodup state reference).map_on
  intro first firstMember second secondMember roots
  apply List.inj_on_of_nodup_map (slots_endpoints_nodup state reference) firstMember secondMember
  have firstValid := slots_valid state reference first firstMember
  have secondValid := slots_valid state reference second secondMember
  have sameTree : first.primary.toRaw = second.primary.toRaw := by
    rw [← firstValid.located,← secondValid.located,roots]
  rw [firstValid.continuation,secondValid.continuation,roots,sameTree]

theorem slots_length {lower upper : Nat} (state : State) (reference : BST lower upper) :
    (slots state reference).length = reference.size + 1 := by
  have lengths := congrArg List.length (slots_keys state reference)
  simpa only [List.length_map,Accounting.forest_length,DynamicOptimality.BST.toRaw_size] using lengths

end MultiSplay.ComparatorForest
