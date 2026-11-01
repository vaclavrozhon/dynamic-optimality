import TaggedTransfer
import UniformBlockRebase
import OrderedGrowerUniformity

/-! The actual global label lookup weakly decreases under the concrete
rank-shift rebase. Frozen bases are transported from their actual member
shift; remaining growers have already passed actual mismatch selection. -/

namespace GreedyMerge.StateLabels

open OrderedBlocks Primitives BlockCoverage
open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis

theorem exists_base_iff_represented {n : ℕ} (rank : ℕ → ℕ) (states : States n) (key : ℕ) :
    (∃ base, HasBase rank states key base) ↔ Represented states key := by
  constructor
  · rintro ⟨base, owner, side, entry, member, equal⟩
    exact ⟨owner, side, entry, tagged_member_entry _ _ _ _ member, equal⟩
  · rintro ⟨owner, side, entry, member, equal⟩
    rw [← tagged_entries (rank owner.val) (states owner side)] at member
    obtain ⟨⟨actualEntry, base⟩, present, same⟩ := List.mem_map.mp member
    have sameEntry : actualEntry = entry := same
    exact ⟨base, owner, side, actualEntry, present, (congrArg Entry.key sameEntry).trans equal⟩

theorem label_of_absent {n : ℕ} (rank : ℕ → ℕ) (K : ℤ) (states : States n) (key : ℕ)
    (absent : ¬ Represented states key) : label rank K states key = K := by
  unfold label
  exact dif_neg (fun existsBase => absent ((exists_base_iff_represented rank states key).mp existsBase))

theorem rebaseAll_represented {n : ℕ} (before after : BST 0 n) (states : States n) (key : ℕ) :
    Represented (rebaseAll before after states) key ↔ Represented states key := by
  simp only [Represented, rebaseAll_entries]

/-- Pointwise global nonincrease, derived directly from actual block
members and the concrete rebase program, with no aggregate bound. -/
theorem rebaseAll_label_le {n : ℕ} (before after tree : BST 0 n) (K : ℤ) (states : States n)
    (valid : ∀ owner side, Valid owner.val side (states owner side))
    (sound : Sound (Snapshot.ofTree after) tree states)
    (upper : ∀ owner side, UpperBase before.externalDepth (states owner side))
    (uniform : ∀ owner side, UniformBlocks (rankShift before after) (states owner side))
    (growerUniform : ∀ owner side, GrowerUniform (rankShift before after) owner.val (states owner side))
    (key : ℕ) :
    label after.externalDepth K (rebaseAll before after states) key ≤
      label before.externalDepth K states key := by
  have newValid := rebaseAll_valid before after states valid
  have newSound := rebaseAll_sound before after tree states sound
  by_cases represented : Represented states key
  · obtain ⟨owner, side, entry, member, equal⟩ := represented
    rcases List.mem_append.mp member with frozen | growing
    · obtain ⟨block, blockMember, entryMember⟩ := List.mem_flatMap.mp frozen
      have newBlock : rebaseFrozen before.externalDepth after.externalDepth owner.val block ∈
          (rebaseAll before after states owner side).shrinking :=
        List.mem_map.mpr ⟨block, blockMember, rfl⟩
      have newEntry : entry ∈
          (rebaseFrozen before.externalDepth after.externalDepth owner.val block).members := entryMember
      rw [← equal,
        label_of_frozen (Snapshot.ofTree after) tree after.externalDepth K _ newValid newSound
          owner side _ newBlock entry newEntry,
        label_of_frozen (Snapshot.ofTree after) tree before.externalDepth K states valid sound
          owner side block blockMember entry entryMember]
      exact (rebaseAll_numeric before after tree states upper sound uniform).2
        owner side block blockMember entry entryMember
    · have newGrowing : entry ∈ growerEntries (rebaseAll before after states owner side).grower := growing
      rw [← equal,
        label_of_growing (Snapshot.ofTree after) tree after.externalDepth K _ newValid newSound
          owner side entry newGrowing,
        label_of_growing (Snapshot.ofTree after) tree before.externalDepth K states valid sound
          owner side entry growing]
      have shift := growerUniform owner side entry growing
      unfold rankShift at shift
      have sameGap : after.externalDepth entry.key - after.externalDepth owner.val =
          before.externalDepth entry.key - before.externalDepth owner.val := by omega
      rw [sameGap]
  · rw [label_of_absent before.externalDepth K states key represented,
      label_of_absent after.externalDepth K _ key
        (fun present => represented ((rebaseAll_represented before after states key).mp present))]

end GreedyMerge.StateLabels

#print axioms GreedyMerge.StateLabels.rebaseAll_label_le
