import MultiSplay.RichRestrictionStable
import MultiSplay.InterfacePlacementFrame

/-!
# Separation after retiring the boundary of a restricted component

Internal records retain their original IDs. Global records can only lose
payloads and become shrinking during retirement. Once the new root is
unassigned, every record outside the restriction is passive for that component.
-/

namespace MultiSplay.RichRestriction

open Splay.Lazy (State HeapView Block Element)

variable {n m : Nat}

theorem separated {params : Splay.Interface.Parameters}
    (source : State m) (small : HeapView n) (embedding : Embedding small source.view)
    (stable : source.Stable params) (post : Splay.Interface.State m)
    (lengthEq : post.blocks.length = source.blocks.length)
    (retired : ∀ id : Fin source.blocks.length, ∃ block,
      post.block? id.val = some block ∧ block.creator = (source.blocks.get id).creator ∧
      (block.mode = .growing → (source.blocks.get id).mode = .growing) ∧
      block.elements.Sublist (source.blocks.get id).elements)
    (rootFree : embedding.element small.root ∉ post.allElements)
    (placement : InterfacePlacement.Placement (state source small embedding).toInterface post)
    (elements : placement.element = embedding.element)
    (ids : ∀ i, placement.id i = (origin source small embedding ⟨i.val, by simpa [State.toInterface] using i.isLt⟩).val) :
    placement.Separated := by
  intro globalId absent
  let oldId : Fin source.blocks.length := ⟨globalId.val, by simpa only [← lengthEq] using globalId.isLt⟩
  obtain ⟨block, found, creator, growing, payload⟩ := retired oldId
  have currentEq : post.blocks.get globalId = block := (List.getElem?_eq_some_iff.mp found).2
  have outside : (source.blocks.get oldId).owner ∉ Set.range embedding.element := by
    intro inside
    obtain ⟨localId, originEq⟩ := origin_surjective_on source small embedding oldId inside
    let i : Fin (state source small embedding).toInterface.blocks.length := ⟨localId.val, by simpa [State.toInterface] using localId.isLt⟩
    apply absent i
    rw [ids]
    exact congrArg Fin.val originEq
  constructor
  · intro x present old same
    rw [currentEq] at present
    rw [elements] at same
    have oldPresent := payload.subset present
    have notRoot : old ≠ small.root := by
      intro isRoot
      apply rootFree
      apply List.mem_flatMap.mpr
      refine ⟨block, List.mem_of_getElem? found, ?_⟩
      simpa only [same, isRoot] using present
    obtain ⟨owner, parent⟩ := Option.ne_none_iff_exists'.mp (small.parent_ne_none_of_ne_root notRoot)
    have child := small.mem_topDown_iff.mpr ⟨parent, rfl⟩
    have globalChild : embedding.element old ∈ source.view.topDown (embedding.element owner) (small.side old) := by
      rw [embedding.children]
      exact List.mem_map.mpr ⟨old, child, rfl⟩
    have oldParent := (stable.valid.2 _ (List.get_mem _ oldId)).parent_eq oldPresent
    rw [same] at oldParent
    have ownerEq : embedding.element owner = (source.blocks.get oldId).owner :=
      Option.some.inj ((source.view.mem_topDown_parent globalChild).symm.trans oldParent)
    exact outside ⟨owner, ownerEq⟩
  · intro mode old same
    rw [currentEq] at mode same
    rw [elements, creator] at same
    have ownerEq := (stable.valid.2 _ (List.get_mem _ oldId)).2.1 (growing mode)
    exact outside ⟨old, (ownerEq.trans same).symm⟩

end MultiSplay.RichRestriction
