import Greedy.SparseCreatorSum
import Greedy.StoredGrowthWindows
import Greedy.LabelSnapshots

/-!
# The creator bound from literal stored pairs and actual growth books

Only the signed bound for each complete family remains a premise here.
The number of simultaneous growth windows and support of each coefficient
are derived from the actual preserved growth book, not assumed.
-/

namespace Greedy.GrowthJournal

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.GrowthBook
open GreedyForest
open scoped BigOperators

variable {Edge : Type*} [Fintype Edge]

theorem stored_coefficient_bound {n clock next : ℕ} {states : HeapSides n}
    (books : HeapBooks n) (good : HeapGood clock next states books)
    (block : Edge → Frozen) (winner loser : Edge → Entry) (creator : Edge → External n)
    (correct : ∀ edge, (creator edge).val = (block edge).creator)
    (covered : ∀ edge, Covered books (block edge))
    (winnerMem : ∀ edge, winner edge ∈ (block edge).members)
    (loserMem : ∀ edge, loser edge ∈ (block edge).members)
    (familyBound : ∀ record family time,
      |∑ edge, if creator edge = record ∧ (block edge).family = family then
        joinCoefficient (winner edge).joined (loser edge).joined time else 0| ≤ 3)
    (record : External n) (time : ℕ) :
    |∑ edge, if creator edge = record then joinCoefficient (winner edge).joined (loser edge).joined time else 0| ≤ 6 := by
  classical
  let names := Finset.univ.image (fun edge => (block edge).family)
  let active := activeNames books record time names
  let mass := fun family => ∑ edge, if creator edge = record ∧ (block edge).family = family then
    joinCoefficient (winner edge).joined (loser edge).joined time else 0
  have partition : (∑ family ∈ active, mass family) =
      ∑ edge, if creator edge = record then joinCoefficient (winner edge).joined (loser edge).joined time else 0 := by
    dsimp only [mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases same : creator edge = record
    · by_cases nonzero : joinCoefficient (winner edge).joined (loser edge).joined time ≠ 0
      · obtain ⟨actual, side, creatorEq, started, unfinished⟩ :=
          (covered edge).nonzero_active (winner edge) (loser edge) (winnerMem edge) (loserMem edge) time nonzero
        have actualEq : actual = record := Fin.ext (creatorEq.trans ((correct edge).symm.trans (congrArg Fin.val same)))
        subst actual
        have activeMem : (block edge).family ∈ active :=
          Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨edge, Finset.mem_univ _, rfl⟩, side, started, unfinished⟩
        simp [same, activeMem]
      · have zero := not_ne_iff.mp nonzero
        simp [same, zero]
    · simp [same]
  rw [← partition]
  calc
    |∑ family ∈ active, mass family| ≤ ∑ family ∈ active, |mass family| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _family ∈ active, (3 : ℤ) := Finset.sum_le_sum (fun family _ => familyBound record family time)
    _ = (active.card : ℤ)*3 := by simp
    _ ≤ 6 := by
      have bound : (active.card : ℤ) ≤ 2 := by exact_mod_cast activeNames_card books good record time names
      omega

theorem stored_creator_shift {n clock next : ℕ} {states : HeapSides n}
    (history : LabelHistory.History (External n)) (books : HeapBooks n) (good : HeapGood clock next states books)
    (block : Edge → Frozen) (winner loser : Edge → Entry) (creator : Edge → External n)
    (correct : ∀ edge, (creator edge).val = (block edge).creator)
    (covered : ∀ edge, Covered books (block edge))
    (winnerMem : ∀ edge, winner edge ∈ (block edge).members)
    (loserMem : ∀ edge, loser edge ∈ (block edge).members)
    (winnerSnapshot : ∀ edge, LabelSnapshots.Snapshot history (block edge).creator (winner edge))
    (loserSnapshot : ∀ edge, LabelSnapshots.Snapshot history (block edge).creator (loser edge))
    (familyBound : ∀ record family time,
      |∑ edge, if creator edge = record ∧ (block edge).family = family then
        joinCoefficient (winner edge).joined (loser edge).joined time else 0| ≤ 3) :
    (∑ edge, ((loser edge).creatorLabel - (winner edge).creatorLabel)) ≤ 6 * LabelHistory.variation history := by
  have snapshots (edge : Edge) : (loser edge).creatorLabel - (winner edge).creatorLabel =
      LabelHistory.value history (loser edge).joined (creator edge) -
        LabelHistory.value history (winner edge).joined (creator edge) := by
    rw [(loserSnapshot edge).2, (winnerSnapshot edge).2, ← correct edge]
    simp only [LabelSnapshots.atKey_record]
  simp_rw [snapshots]
  exact LabelHistory.sparse_creator_bound history creator (fun edge => (winner edge).joined) (fun edge => (loser edge).joined) 6
    (stored_coefficient_bound books good block winner loser creator correct covered winnerMem loserMem familyBound)

end Greedy.GrowthJournal
