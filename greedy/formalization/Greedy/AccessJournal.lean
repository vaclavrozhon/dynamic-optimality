import Greedy.AccessTrace
import Greedy.JournalVariation

/-!
# Access links in the same chronological entry journal

Each actual link contributes its immutable entry followed by the one
loser-label update. Prefix labels agree with the executed block states.
Internal means membership in the same frozen source instance, including
equal labels; no strict-label hypothesis is imposed.
-/

namespace Greedy.AccessJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks GreedyMerge.PathPlateau
open EntryJournal GreedyForest.Phase

variable {n : ℕ}

def program (rank : ℕ → ℕ) (kind : External n × External n → Kind) :
    List (External n × External n) → List (Action (External n))
  | [] => []
  | event :: rest => .entry event.2 event.1 (kind event) ::
      .change event.2 (contractedGap (rank event.2.val - rank event.1.val)) :: program rank kind rest

def advance (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (state : WeightedMemory.State (External n)) (event : External n × External n) : WeightedMemory.State (External n) :=
  step (step state (.entry event.2 event.1 (kind event)))
    (.change event.2 (contractedGap (rank event.2.val - rank event.1.val)))

theorem advance_labels (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (initial : ℕ → ℤ) (state : WeightedMemory.State (External n)) (event : External n × External n)
    (agree : ∀ record, state.label record = initial record.val) :
    ∀ record, (advance rank kind state event).label record = linkLabels rank initial (eventKeys event) record.val := by
  intro record
  by_cases same : record = event.2
  · subst record; simp [advance, step, encode, WeightedMemory.step, linkLabels, eventKeys]
  · have different : record.val ≠ event.2.val := fun equal => same (Fin.ext equal)
    simp [advance, step, encode, WeightedMemory.step, linkLabels, eventKeys, same, different, agree]

theorem program_labels (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (events : List (External n × External n)) (initial : ℕ → ℤ)
    (state : WeightedMemory.State (External n)) (agree : ∀ record, state.label record = initial record.val) :
    ∀ record, (run state (program rank kind events)).label record = runLabels rank initial (events.map eventKeys) record.val := by
  induction events generalizing initial state with
  | nil => exact agree
  | cons event rest ih =>
      exact ih (linkLabels rank initial (eventKeys event)) (advance rank kind state event)
        (advance_labels rank kind initial state event agree)

theorem program_valid (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (events : List (External n × External n)) (initial : ℕ → ℤ) (H : ℕ)
    (height : ∀ record : External n, rank record.val ≤ H)
    (state : WeightedMemory.State (External n)) (agree : ∀ record, state.label record = initial record.val)
    (ordered : ∀ index : Fin events.length, kind (events.get index) = .internal →
      labelsAt rank initial (events.map eventKeys) index.val (events.get index).1.val ≤
        labelsAt rank initial (events.map eventKeys) index.val (events.get index).2.val) :
    EntryJournal.Valid (contractedGap H) state (program rank kind events) := by
  induction events generalizing initial state with
  | nil => trivial
  | cons event rest ih =>
      have head : legal (contractedGap H) state (.entry event.2 event.1 (kind event)) := by
        intro internal
        have order := ordered ⟨0, by simp⟩ internal
        change initial event.1.val ≤ initial event.2.val at order
        change state.label event.1 ≤ state.label event.2
        simpa only [agree] using order
      have valueBound : 1 ≤ (contractedGap (rank event.2.val - rank event.1.val) : ℤ) ∧
          (contractedGap (rank event.2.val - rank event.1.val) : ℤ) ≤ contractedGap H := by
        constructor
        · unfold contractedGap; omega
        · exact_mod_cast contractedGap_mono ((Nat.sub_le _ _).trans (height event.2))
      refine ⟨head, valueBound, ih (linkLabels rank initial (eventKeys event)) (advance rank kind state event)
        (advance_labels rank kind initial state event agree) ?_⟩
      intro index internal
      have order := ordered ⟨index.val+1, by simp only [List.length_cons]; omega⟩ internal
      simpa only [List.get_eq_getElem, List.getElem_cons_succ, labelsAt, List.map_cons,
        List.take_succ_cons, runLabels, List.foldl_cons] using order

/-- The journal's prefix snapshot is exactly the pre-link block-state
snapshot, not just a label sequence with the same endpoint. -/
theorem actual_prefix {access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source) (K : ℤ) (clock : ℕ)
    (states : States n) (ready : Ready comparator oldTree states)
    (empty : ∀ side, growerEntries (states source side).grower = [])
    (state : WeightedMemory.State (External n)) (agree : state.label = RestorationJournal.labels comparator K states)
    (index : ℕ) (inside : index ≤ data.events.length) :
    (run state (program comparator.externalDepth (AccessTrace.kind states source) (data.events.take index))).label =
      RestorationJournal.labels comparator K (AccessTrace.current comparator K source clock states data.events index) := by
  have actual := AccessTrace.prefix_labels data source geometry K clock states ready empty index inside
  funext record
  rw [program_labels _ _ _ (GreedyMerge.StateLabels.label comparator.externalDepth K states) state
    (by intro key; rw [agree]; rfl)]
  rw [List.map_take]
  exact (congrFun actual record.val).symm

theorem actual_valid {access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source) (H : ℕ) (clock : ℕ)
    (height : comparator.height ≤ H)
    (states : States n) (ready : Ready comparator oldTree states)
    (empty : ∀ side, growerEntries (states source side).grower = [])
    (state : WeightedMemory.State (External n)) (agree : state.label = RestorationJournal.labels comparator (contractedGap H) states) :
    EntryJournal.Valid (contractedGap H) state
      (program comparator.externalDepth (AccessTrace.kind states source) data.events) := by
  apply program_valid comparator.externalDepth (AccessTrace.kind states source) data.events
    (GreedyMerge.StateLabels.label comparator.externalDepth (contractedGap H) states) H
    (fun record => (externalDepth_le_height comparator record.val).trans height) state
    (by intro key; rw [agree]; rfl)
  intro index internal
  have order := AccessTrace.internal_order data source geometry (contractedGap H) clock states ready empty index internal
  dsimp only at order
  rw [AccessTrace.prefix_labels data source geometry (contractedGap H) clock states ready empty index.val
    (Nat.le_of_lt index.isLt)] at order
  exact order

theorem program_ordinary_zero (rank : ℕ → ℕ) (kind : External n × External n → Kind)
    (events : List (External n × External n)) (ordinaryFree : ∀ event ∈ events, kind event ≠ .ordinary)
    (state : WeightedMemory.State (External n)) : total ordinary state (program rank kind events) = 0 := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      have notOrdinary := ordinaryFree event (by simp)
      have tail := ih (fun next member => ordinaryFree next (by simp [member])) (advance rank kind state event)
      cases kindEq : kind event <;> simp_all [program, total, ordinary, advance]

end Greedy.AccessJournal
