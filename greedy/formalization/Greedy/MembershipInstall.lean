import Greedy.MembershipStamps

/-! Family stamps of newly installed and appended memberships. -/

namespace Greedy.MembershipStamps

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

theorem tagged_installPaid (owner : ℕ) (side : Bool) (splitStart id paidFamily base : ℕ)
    (entry : Entry) (state : SideState) (item : Entry) (family : ℕ)
    (member : (item, family) ∈ tagged (installPaid owner side splitStart id paidFamily base entry state)) :
    (item, family) ∈ tagged state ∨ (item = entry ∧ family = paidFamily) := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, itemMem, familyEq⟩ |
    ⟨grower, present, itemMem, familyEq⟩
  · change block ∈ (separateOuter side entry.key splitStart state).1 ++
      [singleton id paidFamily owner base entry] ++ (separateOuter side entry.key splitStart state).2 at blockMem
    have inherited (part : block ∈ (separateOuter side entry.key splitStart state).1 ++
        (separateOuter side entry.key splitStart state).2) : (item, family) ∈ tagged state := by
      obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side entry.key splitStart state block part
      have same : original.family = family := descendant.1.symm.trans familyEq
      rw [← same]
      exact tagged_frozen state original originalMem item (descendant.2.2.subset itemMem)
    rcases List.mem_append.mp blockMem with first | last
    · rcases List.mem_append.mp first with old | fresh
      · exact Or.inl (inherited (List.mem_append_left _ old))
      · have same := List.mem_singleton.mp fresh
        subst block
        exact Or.inr ⟨List.mem_singleton.mp itemMem, familyEq.symm⟩
    · exact Or.inl (inherited (List.mem_append_right _ last))
  · left
    rw [← familyEq]
    exact tagged_growing state grower present item itemMem


theorem tagged_append (state : SideState) (grower : Grower) (present : state.grower = some grower)
    (entry item : Entry) (family : ℕ) (member : (item, family) ∈ tagged (appendGrower entry state)) :
    (item, family) ∈ tagged state ∨ (item = entry ∧ family = grower.family) := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, entryMem, familyEq⟩ |
    ⟨next, nextPresent, entryMem, familyEq⟩
  · left
    rw [← familyEq]
    exact tagged_frozen state block blockMem item entryMem
  · have equal : grow entry grower = next := by simpa [appendGrower, present] using nextPresent
    rw [← equal] at entryMem familyEq
    rcases List.mem_append.mp entryMem with previous | fresh
    · left
      rw [← familyEq]
      exact tagged_growing state grower present item previous
    · exact Or.inr ⟨List.mem_singleton.mp fresh, familyEq.symm⟩

end Greedy.MembershipStamps
