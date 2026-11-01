import Greedy.RunCreatorSum
import Greedy.StoredGrowthWindows

/-! Actual family cancellation and the two creator slots give capacity six. -/

namespace Greedy.GrowthJournal

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GreedyMerge.FrozenHistory GreedyForest

theorem Covered.crossing_active {n : ℕ} {books : HeapBooks n} {block : Frozen}
    (covered : Covered books block) (time : ℕ)
    (crosses : Straddles (fun joined => decide (time+1 ≤ joined)) (joins block)) :
    ∃ creator side, creator.val = block.creator ∧
      growthStart block.family (journal (books creator side)) ≤ time ∧
        time < growthEnd block.family (journal (books creator side)) := by
  obtain ⟨early, earlyMem, late, lateMem, below, above⟩ := (straddles_nat_cut_iff (time+1) _).mp crosses
  obtain ⟨first, firstMem, firstTime⟩ := List.mem_map.mp (List.mem_toFinset.mp earlyMem)
  obtain ⟨second, secondMem, secondTime⟩ := List.mem_map.mp (List.mem_toFinset.mp lateMem)
  rcases covered with batch | constant
  · obtain ⟨creator, side, correct, between⟩ := batch.between
    have firstBounds := between first firstMem
    have secondBounds := between second secondMem
    exact ⟨creator, side, correct, by omega, by omega⟩
  · have same := constant first firstMem second secondMem
    omega

end Greedy.GrowthJournal

namespace Greedy.CreatorPhase

open Splay.Tree Splay.Tree.BST Splay.Rank GreedyMerge.GrowthBook GreedyMerge.GrowthWindows GrowthJournal
open scoped BigOperators

theorem total_nonzero_active {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (books : HeapBooks n) (covered : AllSourcesCovered books execution) (record : External n) (family time : ℕ)
    (nonzero : total execution record.val family time ≠ 0) :
    ∃ side, growthStart family (journal (books record side)) ≤ time ∧ time < growthEnd family (journal (books record side)) := by
  induction execution with
  | done => exact False.elim (nonzero rfl)
  | @rotate first last after depth requests rotation data afterValid rest ih => exact ih afterValid covered.2 nonzero
  | @access first last requests request root decomposition data afterValid rest ih =>
      by_cases headZero : familyCoefficient data (RunJournal.prepared first request) (Execution.source request) record.val family time = 0
      · exact ih afterValid covered.2.2 (by simpa only [total, headZero, zero_add] using nonzero)
      · obtain ⟨side, block, member, creator, named, contributes⟩ :=
          nonzero_piece data (RunJournal.prepared first request) (Execution.source request) record.val family time headZero
        have crosses := part_nonzero_crosses data (RunJournal.prepared first request) (Execution.source request) side block time
          ((prepared_ready first request valid).valid _ side) member contributes
        obtain ⟨actual, direction, actualCreator, started, active⟩ :=
          (covered.2.1 (Execution.source request) side block member).crossing_active time crosses
        have actualEq : actual = record := Fin.ext (actualCreator.trans creator)
        exact ⟨direction, by simpa only [actualEq, named] using started, by simpa only [actualEq, named] using active⟩

theorem summed_coefficient_bound {n clock next : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (inv : FamilyOrder.Invariant first.clock first.next first.blocks)
    (books : HeapBooks n) {states : GreedyMerge.OrderedBlocks.HeapSides n} (good : HeapGood clock next states books)
    (covered : AllSourcesCovered books execution) (names : Finset ℕ) (record : External n) (time : ℕ) :
    |∑ family ∈ names, total execution record.val family time| ≤ 6 := by
  classical
  let active := activeNames books record time names
  have restrict : (∑ family ∈ names, total execution record.val family time) =
      ∑ family ∈ active, total execution record.val family time := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro family member outside
    by_contra nonzero
    exact outside (Finset.mem_filter.mpr ⟨member, total_nonzero_active execution valid books covered record family time nonzero⟩)
  rw [restrict]
  calc
    _ ≤ ∑ family ∈ active, |total execution record.val family time| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _family ∈ active, (3 : ℤ) := Finset.sum_le_sum (fun family _ => total_abs_le_three execution valid inv record.val family time)
    _ = (active.card : ℤ)*3 := by simp
    _ ≤ 6 := by
      have bound : (active.card : ℤ) ≤ 2 := by exact_mod_cast activeNames_card books good record time names
      omega

theorem initialized_summed_coefficient_bound {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests)
    (names : Finset ℕ) (record : External n) (time : ℕ) :
    |∑ family ∈ names, total execution record.val family time| ≤ 6 := by
  obtain ⟨books, inv, covered⟩ := GrowthJournal.initialized_all_sources initial comparator K execution
  exact summed_coefficient_bound execution (Execution.initial_valid initial comparator K)
    (FamilyOrder.initial_invariant (Splay.Rank.Snapshot.ofTree comparator) _ K)
    books inv.good covered names record time

end Greedy.CreatorPhase
