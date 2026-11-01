import Greedy.FamilyInvariant
import Greedy.StoredGrowthWindows

/-! The unique straddling fragment is a literal frozen block in the heap. -/

namespace Greedy.FamilyOrder

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.FrozenHistory GreedyMerge.HistoryProcess GreedyForest

theorem mem_allFrozen {Slot : Type*} [Fintype Slot] (states : Slot → SideState) (slot : Slot)
    (block : Frozen) (member : block ∈ (states slot).shrinking) : block ∈ allFrozen states :=
  List.mem_flatMap.mpr ⟨slot, by simp, member⟩

theorem heap_mem_allFrozen {n : ℕ} (states : HeapSides n) (owner : External n) (side : Bool)
    (block : Frozen) (member : block ∈ (states owner side).shrinking) : block ∈ allFrozen (table states) :=
  mem_allFrozen (table states) (encode n (owner, side)) block (by simpa [table] using member)

theorem Invariant.uniqueStraddler {n clock next : ℕ} {states : HeapSides n}
    (inv : Invariant clock next states) (family cut : ℕ) :
    UniqueStraddler (fun joined => decide (cut ≤ joined)) (familyView family (allFrozen (table states))) :=
  orderedFamily_uniqueStraddler cut _ (family_ordered (table states) inv.ordered family)

theorem coefficient_straddles (block : Frozen) (winner loser : Entry) (time : ℕ)
    (winnerMem : winner ∈ block.members) (loserMem : loser ∈ block.members)
    (nonzero : joinCoefficient winner.joined loser.joined time ≠ 0) :
    GreedyForest.Straddles (fun joined => decide (time+1 ≤ joined)) (joins block) := by
  have winnerJoin : winner.joined ∈ joins block := List.mem_toFinset.mpr (List.mem_map.mpr ⟨winner, winnerMem, rfl⟩)
  have loserJoin : loser.joined ∈ joins block := List.mem_toFinset.mpr (List.mem_map.mpr ⟨loser, loserMem, rfl⟩)
  apply (straddles_nat_cut_iff (time+1) (joins block)).mpr
  by_cases winnerAfter : time < winner.joined
  · by_cases loserAfter : time < loser.joined
    · simp [joinCoefficient, winnerAfter, loserAfter] at nonzero
    · exact ⟨loser.joined, loserJoin, winner.joined, winnerJoin, by omega, by omega⟩
  · by_cases loserAfter : time < loser.joined
    · exact ⟨winner.joined, winnerJoin, loser.joined, loserJoin, by omega, by omega⟩
    · simp [joinCoefficient, winnerAfter, loserAfter] at nonzero

theorem straddling_block_unique (blocks : List Frozen) (valid : GreedyMerge.HistoryProcess.Valid blocks)
    (first second : Frozen) (firstMem : first ∈ blocks) (secondMem : second ∈ blocks)
    (family : first.family = second.family) (cut : ℕ)
    (firstCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins first))
    (secondCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins second)) : first = second := by
  by_contra different
  have separated := separated_of_members blocks valid.1 first second firstMem secondMem different
  obtain ⟨firstEarly, firstEarlyMem, firstLate, firstLateMem, firstBelow, firstAbove⟩ := (straddles_nat_cut_iff cut _).mp firstCross
  obtain ⟨secondEarly, secondEarlyMem, secondLate, secondLateMem, secondBelow, secondAbove⟩ := (straddles_nat_cut_iff cut _).mp secondCross
  rcases separated with other | forward | backward
  · exact other family
  · have crossing := forward firstLate firstLateMem secondEarly secondEarlyMem
    omega
  · have crossing := backward secondLate secondLateMem firstEarly firstEarlyMem
    omega

theorem Invariant.straddling_block_unique {n clock next : ℕ} {states : HeapSides n}
    (inv : Invariant clock next states) (firstOwner secondOwner : External n) (firstSide secondSide : Bool)
    (first second : Frozen) (firstMem : first ∈ (states firstOwner firstSide).shrinking)
    (secondMem : second ∈ (states secondOwner secondSide).shrinking)
    (family : first.family = second.family) (cut : ℕ)
    (firstCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins first))
    (secondCross : GreedyForest.Straddles (fun joined => decide (cut ≤ joined)) (joins second)) : first = second :=
  Greedy.FamilyOrder.straddling_block_unique _ (allFrozen_valid (table states) inv.ordered) first second
    (heap_mem_allFrozen states firstOwner firstSide first firstMem) (heap_mem_allFrozen states secondOwner secondSide second secondMem)
    family cut firstCross secondCross

end Greedy.FamilyOrder
