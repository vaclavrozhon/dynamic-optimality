import Greedy.SnapshotTransport

/-! Paid restoration preserves old snapshots and captures one new pair. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation

theorem tagged_installPaid (owner : ℕ) (side : Bool) (splitStart id family base : ℕ)
    (entry : Entry) (state : SideState) (item : Entry) (creator : ℕ)
    (member : (item, creator) ∈ tagged (installPaid owner side splitStart id family base entry state)) :
    (item, creator) ∈ tagged state ∨ (item = entry ∧ creator = owner) := by
  rcases tagged_cases _ _ _ member with ⟨block, blockMem, itemMem, creatorEq⟩ |
    ⟨grower, present, itemMem, creatorEq⟩
  · change block ∈ (separateOuter side entry.key splitStart state).1 ++
      [singleton id family owner base entry] ++ (separateOuter side entry.key splitStart state).2 at blockMem
    have inherited (part : block ∈ (separateOuter side entry.key splitStart state).1 ++
        (separateOuter side entry.key splitStart state).2) : (item, creator) ∈ tagged state := by
      obtain ⟨original, originalMem, descendant⟩ := separateOuter_descends side entry.key splitStart state block part
      have same : original.creator = creator := descendant.2.1.symm.trans creatorEq
      rw [← same]
      exact tagged_frozen state original originalMem item (descendant.2.2.subset itemMem)
    rcases List.mem_append.mp blockMem with first | last
    · rcases List.mem_append.mp first with old | fresh
      · exact Or.inl (inherited (List.mem_append_left _ old))
      · have same := List.mem_singleton.mp fresh
        subst block
        exact Or.inr ⟨List.mem_singleton.mp itemMem, creatorEq.symm⟩
    · exact Or.inl (inherited (List.mem_append_right _ last))
  · left
    rw [← creatorEq]
    exact tagged_growing state grower present item itemMem

theorem restorePort_snapshots {n : ℕ} {history : LabelHistory.History (External n)}
    (snapshot : Splay.Rank.Snapshot n) (tree : BST 0 n) (names : PaidNames)
    (makeEntry : External n → Entry) (record : External n) (states : States n)
    (snapshots : HeapSnapshots history states)
    (fresh : ∀ owner, Snapshot history owner.val (makeEntry owner)) :
    HeapSnapshots history (restorePort snapshot tree names makeEntry record states).1 := by
  intro current side item creator member
  cases parent : canonicalParent snapshot tree record with
  | none => exact snapshots current side item creator (by simpa [restorePort, parent] using member)
  | some owner =>
      simp only [restorePort, parent, replaceSide] at member
      split_ifs at member with selected
      · obtain ⟨sameOwner, sameSide⟩ := selected
        subst current
        subst side
        rcases tagged_installPaid owner.val _ _ _ _ _ _ _ item creator member with old | ⟨rfl, rfl⟩
        · exact snapshots owner _ item creator (by simpa using old)
        · exact fresh owner
      · exact snapshots current side item creator member

end Greedy.LabelSnapshots
