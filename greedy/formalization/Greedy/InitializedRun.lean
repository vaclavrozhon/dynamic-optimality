import Greedy.InitialJournal

/-!
# The initialized journal and its unconditional accounting rows

This constructs the same journal from actual initial memberships and the
whole shared execution. Entry deficits, loser shifts, and negative label
variation are bounded by the journal's measured quantities.
`InitializedJoint` extends this construction with all geometric lifetime
charges and the internal-link bound used by `Greedy.Competitive`.
-/

namespace Greedy.InitializedRun

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open EntryJournal RestorationJournal

theorem exists_journal {n : ℕ} (initial comparator : BST 0 n) (H : ℕ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run (contractedGap H) (Execution.initial initial comparator (contractedGap H)) last requests)
    (bounded : execution.Bounded H) :
    let first := Execution.initial initial comparator (contractedGap H)
    let label := labels comparator (contractedGap H) first.blocks
    let state : WeightedMemory.State (External n) := ⟨label, label⟩
    ∃ actions : List (Action (External n)),
      EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels last.comparator (contractedGap H) last.blocks ∧
      total ordinary state actions ≤ 2*n+1 + 11*execution.rotations ∧
      total internal state actions + total boundary state actions = execution.links ∧
      total negativeChange state actions ≤ ((contractedGap H : ℤ)-1)*(2*n+1) + total positiveChange state actions ∧
      total shift state actions ≤ total positiveChange state actions +
        ((contractedGap H : ℤ)-1)*(2*n+1 + 11*execution.rotations) + total positiveEntry state actions ∧
      total deficit state actions ≤ (contractedGap H : ℤ)*(2*n+1 + 11*execution.rotations) +
        total good state actions + total boundary state actions + total negativeEntry state actions := by
  let first := Execution.initial initial comparator (contractedGap H)
  let label := labels comparator (contractedGap H) first.blocks
  let state : WeightedMemory.State (External n) := ⟨label, label⟩
  let entries := InitialJournal.program comparator first.refined.tree
  let entered := run state entries
  have initialValid := InitialJournal.install_valid
    (Splay.Lazy.Canonical.canonicalParent (Splay.Rank.Snapshot.ofTree comparator) first.refined.tree)
    Finset.univ.toList (contractedGap H) state
  have enteredLabel : entered.label = labels first.comparator (contractedGap H) first.blocks :=
    InitialJournal.program_labels comparator first.refined.tree state
  obtain ⟨tail, tailValid, tailLabels, tailOrdinary, tailCount⟩ :=
    RunJournal.exists_journal H execution bounded (Execution.initial_valid initial comparator (contractedGap H))
      entered enteredLabel
  let actions := entries ++ tail
  have valid : EntryJournal.Valid (contractedGap H) state actions :=
    (valid_append ..).mpr ⟨initialValid, tailValid⟩
  have ordinaryInitial : total ordinary state entries ≤ (2*n+1 : ℕ) := by
    have count := InitialJournal.install_count
      (Splay.Lazy.Canonical.canonicalParent (Splay.Rank.Snapshot.ofTree comparator) first.refined.tree)
      Finset.univ.toList state
    simpa only [entries, InitialJournal.program, Finset.length_toList, Finset.card_univ, Fintype.card_fin] using count
  have ordinaryBound : total ordinary state actions ≤ 2*n+1 + 11*execution.rotations := by
    rw [total_append]
    push_cast at ordinaryInitial
    linarith
  have kinds : OrdinaryOnly entries := InitialJournal.install_ordinary _ _
  have height : comparator.height ≤ H := RunJournal.initial_height execution H bounded
  have labelBound : Bounded (contractedGap H) state :=
    fun record => GreedyMerge.StateLabels.label_bounded comparator.externalDepth H first.blocks record
      ((externalDepth_le_height comparator record.val).trans height)
  have negative := negative_bound (contractedGap H) state actions labelBound valid
  have loser := loser_bound (contractedGap H) label actions labelBound valid
  have cap : 1 ≤ (contractedGap H : ℤ) := by unfold contractedGap; omega
  have deficits := deficits_bound (contractedGap H) cap state actions labelBound valid
  refine ⟨actions, valid, ?_, ordinaryBound, ?_, ?_, ?_, ?_⟩
  · rw [run_append]; exact tailLabels
  · rw [total_append, total_append, ordinaryOnly_internal_zero state entries kinds,
      ordinaryOnly_boundary_zero state entries kinds, zero_add, zero_add]
    exact tailCount
  · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using negative
  · nlinarith
  · nlinarith

end Greedy.InitializedRun
