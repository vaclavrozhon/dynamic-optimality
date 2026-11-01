import MultiSplay.BlockEmbedding

/-!
# Ordered attached-child lists under component embeddings

This transport is local: it allows any unrelated assigned vertices outside the
component, provided none acquires a parent in it. The strict ordinal embedding
preserves both left and right list order, hence every retained interval.
-/

namespace MultiSplay.HeapEmbedding

open Splay.Lazy (HeapView Block Element Side)

variable {n m : Nat}

theorem attachedTopDown (embedding : Element n → Element m)
    (ordered : ∀ a b, (embedding a).val < (embedding b).val ↔ a.val < b.val)
    (before : HeapView n) (after : HeapView m) (assigned : List (Element n))
    (afterAssigned : List (Element m)) (owner : Element n) (side : Side)
    (membership : ∀ element,
      after.parent element = some (embedding owner) ∧ after.side element = side ∧ element ∈ afterAssigned ↔
      ∃ original, before.parent original = some owner ∧ before.side original = side ∧
        original ∈ assigned ∧ embedding original = element) :
    after.attachedTopDown afterAssigned (embedding owner) side =
      (before.attachedTopDown assigned owner side).map embedding := by
  have members : ∀ element,
      element ∈ after.attachedTopDown afterAssigned (embedding owner) side ↔
      element ∈ (before.attachedTopDown assigned owner side).map embedding := by
    intro element
    simpa only [HeapView.mem_attachedTopDown_iff, HeapView.mem_topDown_iff,
      List.mem_map, and_assoc] using membership element
  cases side with
  | left =>
      apply List.Pairwise.eq_of_mem_iff ((after.topDown_ordered (embedding owner)).1.filter _) _ members
      exact List.pairwise_map.mpr (((before.topDown_ordered owner).1.filter _).imp
        (fun {a b} relation => (ordered a b).mpr relation))
  | right =>
      apply List.Pairwise.eq_of_mem_iff ((after.topDown_ordered (embedding owner)).2.filter _) _ members
      exact List.pairwise_map.mpr (((before.topDown_ordered owner).2.filter _).imp
        (fun {a b} relation => (ordered b a).mpr relation))

/-- Assigned vertices outside the selected component form a passive frame. -/
theorem attachedTopDown_framed (embedding : Element n → Element m)
    (injective : Function.Injective embedding)
    (ordered : ∀ a b, (embedding a).val < (embedding b).val ↔ a.val < b.val)
    (before : HeapView n) (after : HeapView m) (assigned : List (Element n))
    (afterAssigned extra : List (Element m)) (owner : Element n) (side : Side)
    (assignment : ∀ element, element ∈ afterAssigned ↔ element ∈ assigned.map embedding ∨ element ∈ extra)
    (links : ∀ element ∈ assigned,
      after.parent (embedding element) = (before.parent element).map embedding ∧
      after.side (embedding element) = before.side element)
    (outside : ∀ element ∈ extra, after.parent element ≠ some (embedding owner)) :
    after.attachedTopDown afterAssigned (embedding owner) side =
      (before.attachedTopDown assigned owner side).map embedding := by
  apply attachedTopDown embedding ordered before after assigned afterAssigned owner side
  intro element
  constructor
  · rintro ⟨parent, childSide, member⟩
    rcases (assignment element).mp member with inside | external
    · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp inside
      rw [(links original originalMem).1] at parent
      obtain ⟨oldOwner, oldParent, sameOwner⟩ := Option.map_eq_some_iff.mp parent
      have ownerEq := injective sameOwner
      exact ⟨original, ownerEq ▸ oldParent, (links original originalMem).2 ▸ childSide, originalMem, rfl⟩
    · exact False.elim (outside element external parent)
  · rintro ⟨original, parent, childSide, member, rfl⟩
    refine ⟨?_, (links original member).2.trans childSide, (assignment _).mpr (Or.inl (List.mem_map.mpr ⟨original, member, rfl⟩))⟩
    rw [(links original member).1, parent]
    rfl

theorem structurallyValid (embedding : Element n → Element m)
    (before : HeapView n) (after : HeapView m) (assigned : List (Element n))
    (afterAssigned : List (Element m)) (source : Block n)
    (valid : source.StructurallyValid before assigned)
    (children : after.attachedTopDown afterAssigned (embedding source.owner) source.side =
      (before.attachedTopDown assigned source.owner source.side).map embedding)
    (gaps : ∀ element ∈ source.elements, after.rawGap (embedding element) = before.rawGap element) :
    (BlockEmbedding.block embedding source).StructurallyValid after afterAssigned := by
  refine ⟨?_, ?_, BlockEmbedding.gapValid embedding before after source valid.2.2 gaps⟩
  · obtain ⟨front, back, eq⟩ := valid.1
    refine ⟨front.map embedding, back.map embedding, ?_⟩
    simpa only [BlockEmbedding.block, children, eq, List.map_append]
  · intro growing
    exact congrArg embedding (valid.2.1 growing)

end MultiSplay.HeapEmbedding
