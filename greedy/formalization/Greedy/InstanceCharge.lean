import Greedy.InstanceDeletion
import Greedy.FamilyPhaseSum

/-!
Charges to a concrete frozen instance. The local condition requires a
charged phase to contain an actual departing loser. This is the condition
used for incoming boundary excess; it excludes charges to a surviving root.
-/

namespace Greedy.InstanceCharge

open Splay.Tree Splay.Tree.BST Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open GreedyMerge.HeapAllocation GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open ClosedInstances
open scoped BigOperators

def Charge (n : ℕ) := ∀ {access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access}, AccessScheduleData comparator oldTree newTree p →
      HeapSides n → External n → Bool → Frozen → ℤ

def LocalBound {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (charge : Charge n)
    (data : AccessScheduleData comparator oldTree newTree p) (states : HeapSides n)
    (source : External n) (side : Bool) (block : Frozen) (range allowance : ℤ) : Prop :=
  0 ≤ charge data states source side block ∧
  charge data states source side block ≤ allowance ∧
  (Small block → charge data states source side block ≤ range) ∧
  (charge data states source side block ≠ 0 →
    ∃ event ∈ data.events, event.2.val ∈ keys block)

noncomputable def phase {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (charge : Charge n)
    (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (id : ℕ) : ℤ :=
  ∑ piece ∈ CreatorPhase.pieces states source,
    if piece.2.id = id then charge data states source piece.1 piece.2 else 0

theorem nonzero_piece {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (charge : Charge n)
    (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (id : ℕ)
    (nonzero : phase charge data states source id ≠ 0) :
    ∃ side block, block ∈ (states source side).shrinking ∧ block.id = id ∧ charge data states source side block ≠ 0 := by
  obtain ⟨⟨side, block⟩, member, contributes⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  by_cases matching : block.id = id
  · exact ⟨side, block, (CreatorPhase.mem_pieces ..).mp member, matching, by simpa only [if_pos matching] using contributes⟩
  · exact False.elim (contributes (if_neg matching))

theorem phase_eq_part {n access next : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (charge : Charge n)
    (data : AccessScheduleData comparator oldTree newTree p)
    (states : HeapSides n) (source : External n) (inventory : HeapInventory states next)
    (side : Bool) (block : Frozen) (member : block ∈ (states source side).shrinking) :
    phase charge data states source block.id = charge data states source side block := by
  classical
  unfold phase
  rw [Finset.sum_eq_single (side, block)]
  · simp only [if_true]
  · intro other otherMem different
    by_cases matching : other.2.id = block.id
    · have unique := instance_unique (table states) inventory (encode n (source, other.1)) (encode n (source, side)) other.2 block
        (by simpa [table] using (CreatorPhase.mem_pieces ..).mp otherMem) (by simpa [table] using member) matching
      have same : other = (side, block) := Prod.ext (congrArg Prod.snd ((encode n).injective unique.1)) unique.2
      exact False.elim (different same)
    · exact if_neg matching
  · intro absent
    exact False.elim (absent ((CreatorPhase.mem_pieces ..).mpr member))

def Bounded {n : ℕ} (charge : Charge n) (range allowance : ℤ) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} : Execution.Run K first last requests → Prop
  | .done _ => True
  | .rotate _ _ _ rest => Bounded charge range allowance rest
  | .access (first := first) request _ _ data _ rest =>
      (∀ side block, block ∈ (RunJournal.prepared first request (Execution.source request) side).shrinking →
        LocalBound charge data (RunJournal.prepared first request) (Execution.source request) side block range allowance) ∧
      Bounded charge range allowance rest

noncomputable def total {n : ℕ} (charge : Charge n) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} : Execution.Run K first last requests → ℕ → ℤ
  | .done _, _ => 0
  | .rotate _ _ _ rest, id => total charge rest id
  | .access (first := first) request _ _ data _ rest, id =>
      phase charge data (RunJournal.prepared first request) (Execution.source request) id + total charge rest id

theorem empty_total_zero {n : ℕ} (charge : Charge n) (range allowance : ℤ) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} (execution : Execution.Run K first last requests)
    (bounded : Bounded charge range allowance execution) (id : ℕ)
    (empty : AllSourcesClosed (id := id) Empty execution) : total charge execution id = 0 := by
  induction execution with
  | done => rfl
  | rotate _ _ _ rest ih => exact ih bounded empty.2
  | @access first last requests request root decomposition data afterValid rest ih =>
      have head : phase charge data (RunJournal.prepared first request) (Execution.source request) id = 0 := by
        by_contra nonzero
        obtain ⟨side, block, member, named, contributes⟩ := nonzero_piece charge data _ _ id nonzero
        obtain ⟨event, eventMem, loser⟩ := (bounded.1 side block member).2.2.2 contributes
        have absent := empty.2.1.frozen (encode n (Execution.source request, side)) block (by simpa [table] using member) named
        rw [absent] at loser
        exact Finset.notMem_empty _ loser
      simp only [total, head, ih bounded.2 empty.2.2, zero_add]

theorem small_total_bound {n : ℕ} (charge : Charge n) (range allowance : ℤ) (rangeNonneg : 0 ≤ range) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} (execution : Execution.Run K first last requests)
    (valid : first.Valid) (bounded : Bounded charge range allowance execution) (id : ℕ)
    (small : AllSourcesClosed (id := id) Small execution) : total charge execution id ≤ range := by
  induction execution with
  | done => exact rangeNonneg
  | rotate _ _ afterValid rest ih => exact ih afterValid bounded small.2
  | @access first last requests request root decomposition data afterValid rest ih =>
      by_cases zero : phase charge data (RunJournal.prepared first request) (Execution.source request) id = 0
      · simpa only [total, zero, zero_add] using ih afterValid bounded.2 small.2.2
      · obtain ⟨side, block, member, named, contributes⟩ := nonzero_piece charge data _ _ id zero
        have localBound := bounded.1 side block member
        have smallBlock := small.2.1.frozen (encode n (Execution.source request, side)) block (by simpa [table] using member) named
        obtain ⟨event, eventMem, loser⟩ := localBound.2.2.2 contributes
        have empty := afterAccess_empty_of_small first request K root decomposition data valid afterValid side block member smallBlock event eventMem loser
        have remaining := all_sources_closed rest empty.1 empty_hereditary empty.2
        rw [named] at remaining
        have tail := empty_total_zero charge range allowance rest bounded.2 id remaining
        have prepared := convertHeap_inventory first.comparator.externalDepth
          (fun owner _ => decide (owner = Execution.source request)) first.next first.blocks valid.2.2.1
        have head := phase_eq_part charge data (RunJournal.prepared first request) _ prepared side block member
        rw [named] at head
        simpa only [total, head, tail, add_zero] using localBound.2.2.1 smallBlock

theorem lifetime_bound {n : ℕ} (charge : Charge n) (range allowance : ℤ)
    (rangeNonneg : 0 ≤ range) (allowanceNonneg : 0 ≤ allowance) {K : ℤ}
    {first last : Execution.State n} {requests : List (Fin n)} (execution : Execution.Run K first last requests)
    (valid : first.Valid) (bounded : Bounded charge range allowance execution) (id : ℕ) :
    total charge execution id ≤ allowance + range := by
  induction execution with
  | done => exact add_nonneg allowanceNonneg rangeNonneg
  | rotate _ _ afterValid rest ih => exact ih afterValid bounded
  | @access first last requests request root decomposition data afterValid rest ih =>
      by_cases zero : phase charge data (RunJournal.prepared first request) (Execution.source request) id = 0
      · simpa only [total, zero, zero_add] using ih afterValid bounded.2
      · obtain ⟨side, block, member, named, contributes⟩ := nonzero_piece charge data _ _ id zero
        have remaining := remaining_sources_small first request K root decomposition data valid afterValid rest side block member
        rw [named] at remaining
        have tail := small_total_bound charge range allowance rangeNonneg rest afterValid bounded.2 id remaining
        have prepared := convertHeap_inventory first.comparator.externalDepth
          (fun owner _ => decide (owner = Execution.source request)) first.next first.blocks valid.2.2.1
        have head := phase_eq_part charge data (RunJournal.prepared first request) _ prepared side block member
        rw [named] at head
        change phase charge data _ _ id + total charge rest id ≤ _
        rw [head]
        exact add_le_add (bounded.1 side block member).2.1 tail

end Greedy.InstanceCharge
