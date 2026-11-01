import Greedy.InitializedJoint
import Greedy.LinearLedger

/-! Numerical closure for one constructed, initialized Greedy execution. -/

namespace Greedy

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open EntryJournal RestorationJournal

set_option maxHeartbeats 1200000 in
theorem execution_link_bound {n : ℕ} (initial comparator : BST 0 n) (H : ℕ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) (Execution.initial initial comparator (contractedGap H)) last requests)
    (bounded : execution.Bounded H) :
    execution.links ≤ 239 * contractedGap H * (3*(2*n+1) + execution.births + 33*execution.rotations) := by
  let first := Execution.initial initial comparator (contractedGap H)
  let label := labels comparator (contractedGap H) first.blocks
  let state : WeightedMemory.State (External n) := ⟨label, label⟩
  obtain ⟨actions, history, _sound, _sources, valid, _labels, ordinaryBound, linkCount, _variation,
    creatorBound, positiveBound, boundaryBound, goodBound, negativeEntryBound, positiveEntryBound,
    _memory, _loserEq, creatorEq, internalBound⟩ :=
    InitializedJoint.exists_journal_history initial comparator H execution bounded
  have height : comparator.height ≤ H := RunJournal.initial_height execution H bounded
  have labelBound : EntryJournal.Bounded (contractedGap H) state :=
    fun record => GreedyMerge.StateLabels.label_bounded comparator.externalDepth H first.blocks record
      ((externalDepth_le_height comparator record.val).trans height)
  have cap : 1 ≤ (contractedGap H : ℤ) := by unfold contractedGap; omega
  have negative := negative_bound (contractedGap H) state actions labelBound valid
  have loser := loser_bound (contractedGap H) label actions labelBound valid
  have deficits := deficits_bound (contractedGap H) cap state actions labelBound valid
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at negative
  have positiveNonnegative : 0 ≤ total positiveChange state actions :=
    total_nonneg positiveChange (fun current action => by cases action <;> simp [positiveChange, EntryJournal.encode, WeightedMemory.positiveChange]) state actions
  have negativeNonnegative : 0 ≤ total negativeChange state actions :=
    total_nonneg negativeChange (fun current action => by cases action <;> simp [negativeChange]) state actions
  have creator : total creatorShift state actions ≤ 9*(total positiveChange state actions + total negativeChange state actions) := by
    rw [creatorEq]
    linarith
  have numerical := LinearLedger.with_initial_credit (contractedGap H) (2*n+1) (11*execution.rotations)
    (2*(2*n+1) + execution.births : ℕ) (22*execution.rotations)
    (total positiveChange state actions) (total negativeChange state actions)
    (total good state actions) (total boundary state actions) (total internal state actions)
    (total deficit state actions) (total shift state actions) (total creatorShift state actions)
    cap (by positivity) (by positivity) (by positivity) (by positivity)
    (by nlinarith only [positiveBound])
    (by nlinarith only [negative]) goodBound boundaryBound
    (by nlinarith only [deficits, ordinaryBound, negativeEntryBound, cap]) internalBound
    (by nlinarith only [loser, ordinaryBound, positiveEntryBound, cap]) creator
  rw [linkCount] at numerical
  have integerBound : (execution.links : ℤ) ≤
      239 * (contractedGap H : ℤ) * (3*(2*(n : ℤ)+1) + execution.births + 33*execution.rotations) := by
    push_cast at numerical
    nlinarith only [numerical]
  exact_mod_cast integerBound

end Greedy
