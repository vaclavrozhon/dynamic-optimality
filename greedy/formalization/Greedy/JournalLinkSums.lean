import Greedy.AccessJournal
import Greedy.AtomicAccess

/-! Journal measurements are sums over the literal links and their old labels. -/

namespace Greedy.AccessJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Analysis
open GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open EntryJournal GreedyForest.Phase
open scoped BigOperators

def pairWeight {n : ℕ} (measure : WeightedMemory.State (External n) → Action (External n) → ℤ)
    (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (state : WeightedMemory.State (External n)) (event : External n × External n) : ℤ :=
  measure state (.entry event.2 event.1 (kind event)) +
    measure (step state (.entry event.2 event.1 (kind event)))
      (.change event.2 (contractedGap (rank event.2.val - rank event.1.val)))

theorem program_indexed_total {n : ℕ} (measure : WeightedMemory.State (External n) → Action (External n) → ℤ)
    (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (state : WeightedMemory.State (External n)) (events : List (External n × External n)) :
    total measure state (program rank kind events) =
      ∑ i : Fin events.length, pairWeight measure rank kind
        (run state (program rank kind (events.take i))) (events.get i) := by
  induction events generalizing state with
  | nil => simp only [program, total, List.length_nil, Fin.sum_univ_zero]
  | cons event rest ih =>
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.take_zero, program, run, List.get_eq_getElem, List.getElem_cons_zero,
        Fin.val_zero, Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ, total, pairWeight]
      rw [ih]
      simp only [pairWeight, List.get_eq_getElem]
      rw [add_assoc]

theorem source_snapshots {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (kind : External n × External n → Kind) (initial : ℕ → ℤ)
    (state : WeightedMemory.State (External n)) (agree : ∀ record, state.label record = initial record.val)
    (i : Fin data.events.length) :
    let current := run state (program comparator.externalDepth kind (data.events.take i))
    current.label (data.events.get i).1 = initial (data.events.get i).1.val ∧
      current.label (data.events.get i).2 = initial (data.events.get i).2.val := by
  have prefixLabels : ∀ record, (run state (program comparator.externalDepth kind (data.events.take i))).label record =
      labelsAt comparator.externalDepth initial (data.events.map eventKeys) i record.val := by
    intro record
    rw [program_labels _ _ _ initial state agree, List.map_take]
    rfl
  have actual := actual_event_source_labels geometry.run geometry.unique initial
    ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  simp only [List.get_eq_getElem, List.getElem_map, eventKeys] at actual
  dsimp only
  rw [prefixLabels, prefixLabels]
  exact actual

theorem program_positive_sum {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (kind : External n × External n → Kind) (initial : ℕ → ℤ)
    (state : WeightedMemory.State (External n)) (agree : ∀ record, state.label record = initial record.val) :
    total positiveChange state (program comparator.externalDepth kind data.events) =
      ∑ i : Fin data.events.length,
        max 0 ((contractedGap (comparator.externalDepth (data.events.get i).2.val - comparator.externalDepth (data.events.get i).1.val) : ℤ) -
          initial (data.events.get i).2.val) := by
  rw [program_indexed_total]
  apply Finset.sum_congr rfl
  intro i _
  have labels := source_snapshots data source geometry kind initial state agree i
  simp only [pairWeight, positiveChange, encode, WeightedMemory.positiveChange, step, WeightedMemory.step, zero_add]
  rw [labels.2]

theorem program_negative_sum {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (kind : External n × External n → Kind) (initial : ℕ → ℤ)
    (state : WeightedMemory.State (External n)) (agree : ∀ record, state.label record = initial record.val) :
    total negativeChange state (program comparator.externalDepth kind data.events) =
      ∑ i : Fin data.events.length,
        max 0 (initial (data.events.get i).2.val -
          (contractedGap (comparator.externalDepth (data.events.get i).2.val - comparator.externalDepth (data.events.get i).1.val) : ℤ)) := by
  rw [program_indexed_total]
  apply Finset.sum_congr rfl
  intro i _
  have labels := source_snapshots data source geometry kind initial state agree i
  simp only [pairWeight, negativeChange, step, encode, WeightedMemory.step, zero_add]
  rw [labels.2]

end Greedy.AccessJournal
