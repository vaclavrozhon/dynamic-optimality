import Greedy.JournalBatches
import Greedy.ExecutionState
import FreshRestorationTrace
import TaggedRestoration

/-!
# The entry journal of literal fresh port restoration

Every nonroot port contributes one ordinary entry followed by its actual
label change. Root ports contribute no entry. The program uses the same
names, intermediate block states, and reader as the fresh allocator.
Neither its variation budget nor its entry count is supplied as a premise.
-/

namespace Greedy.RestorationJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.HeapAllocation
open GreedyMerge.StateLabels
open EntryJournal

noncomputable def labels {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (states : HeapSides n) : External n → ℤ :=
  fun record => label comparator.externalDepth K states record.val

noncomputable def one {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n) : List (Action (External n)) :=
  match canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => []
  | some owner => .entry record owner .ordinary ::
      batch (labels comparator K (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1)

/-- A single paid entry reads the old labels, then changes only its own
record's label. Missing records use the bounded fallback label as usual. -/
theorem one_spec {n : ℕ} (comparator tree : BST 0 n) (H : ℕ)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : HeapSides n) (entryKey : ∀ owner, (makeEntry owner).key = record.val)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator (contractedGap H) states) :
    let actions := one comparator tree (contractedGap H) names makeEntry record states
    EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels comparator (contractedGap H)
        (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1 ∧
      total ordinary state actions ≤ 1 ∧ total positiveChange state actions ≤ (contractedGap H : ℤ) - 1 := by
  classical
  have cap : 1 ≤ (contractedGap H : ℤ) := by unfold contractedGap; omega
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simp only [one, parent, restorePort, EntryJournal.Valid, run, total]; exact ⟨trivial, agree, by omega, by omega⟩
  | some owner =>
      let target := labels comparator (contractedGap H)
        (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1
      let entered := step state (.entry record owner .ordinary)
      have bounded : ∀ key, 1 ≤ target key ∧ target key ≤ (contractedGap H : ℤ) :=
        fun key => label_bounded comparator.externalDepth H _ key (height key)
      have oldBound : Bounded (contractedGap H) entered := by
        intro key
        change 1 ≤ state.label key ∧ state.label key ≤ _
        rw [agree]
        exact label_bounded comparator.externalDepth H states key (height key)
      have free : ∀ key, key ∉ ({record} : Finset (External n)) → target key ≤ entered.label key := by
        intro key outside
        have different : key.val ≠ record.val := by
          intro equal
          exact outside (by simp [Fin.ext equal])
        change label _ _ _ key.val ≤ state.label key
        rw [agree]
        exact le_of_eq (restorePort_label comparator tree (contractedGap H) names makeEntry record states entryKey key.val different)
      have paid := batch_positive_le_ports (contractedGap H) entered target {record} oldBound bounded free
      have zero := relabel_zero ordinary (by intros; rfl) entered target Finset.univ.toList
      change total ordinary entered (batch target) = 0 at zero
      simp only [one, parent, EntryJournal.Valid, run, total]
      refine ⟨⟨by simp [legal], batch_valid _ entered target bounded⟩, ?_, ?_, ?_⟩
      · exact congrArg WeightedMemory.State.label (run_batch entered target)
      · change 1 + total ordinary entered (batch target) ≤ 1
        rw [zero]; omega
      · change 0 + total positiveChange entered (batch target) ≤ _
        simpa using paid

noncomputable def program {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry) :
    List (External n) → ℕ → ℕ → HeapSides n → List (Action (External n))
  | [], _, _, _ => []
  | record :: rest, stage, start, states =>
      let names := portNames (Snapshot.ofTree comparator) tree record start states
      let head := restorePort (Snapshot.ofTree comparator) tree names (reader stage states record) record states
      one comparator tree K names (reader stage states record) record states ++
        program comparator tree K reader rest (stage+1)
          (restoreNext (Snapshot.ofTree comparator) tree record start states) head.1

theorem program_spec {n : ℕ} (comparator tree : BST 0 n) (H : ℕ)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage states record owner, (reader stage states record owner).key = record.val)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator (contractedGap H) states) :
    let actions := program comparator tree (contractedGap H) reader ports stage start states
    let result := freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states
    EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels comparator (contractedGap H) result.states ∧
      total ordinary state actions ≤ ports.length ∧
      total positiveChange state actions ≤ ((contractedGap H : ℤ) - 1) * ports.length := by
  induction ports generalizing stage start states state with
  | nil => exact ⟨trivial, agree, by simp [program, total], by simp [program, total]⟩
  | cons record rest ih =>
      let names := portNames (Snapshot.ofTree comparator) tree record start states
      let head := restorePort (Snapshot.ofTree comparator) tree names (reader stage states record) record states
      let actions := one comparator tree (contractedGap H) names (reader stage states record) record states
      have first := one_spec comparator tree H height names (reader stage states record) record states
        (readerKey stage states record) state agree
      have tail := ih (stage+1) (restoreNext (Snapshot.ofTree comparator) tree record start states) head.1
        (run state actions) first.2.1
      dsimp only
      simp only [program]
      rw [valid_append, run_append, total_append, total_append]
      refine ⟨⟨first.1, tail.1⟩, tail.2.1, ?_, ?_⟩
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith [first.2.2.1, tail.2.2.1]
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith [first.2.2.2, tail.2.2.2]

/-- A preparation batch followed by the literal sequential restoration. -/
noncomputable def administration {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (ports : List (External n)) (stage start : ℕ) (prepared : HeapSides n) :
    List (Action (External n)) :=
  batch (labels comparator K prepared) ++ program comparator tree K reader ports stage start prepared

theorem restore_labels_outside {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage states record owner, (reader stage states record owner).key = record.val)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (record : External n) (outside : record ∉ ports) :
    labels comparator K (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states record =
      labels comparator K states record := by
  let result := freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states
  have keys := freshRestorePorts_entry_property (Snapshot.ofTree comparator) tree reader
    (fun _ record _ entry => entry.key = record.val) readerKey ports stage start states
  change label _ _ _ _ = _
  rw [← freshRestorePorts_eq (Snapshot.ofTree comparator) tree reader ports stage start states]
  apply restorePorts_label comparator tree K result.names result.makeEntry keys ports stage states
  intro member
  obtain ⟨port, member, equal⟩ := List.mem_map.mp member
  exact outside ((Fin.ext equal : port = record) ▸ member)

/-- The endpoint nonincrease theorem for a concrete macro also controls
its preparation batch: restoration preserves every nonport label exactly.
The two charged changes per port account for both temporary detachment
and subsequent insertion, including all intermediate reader snapshots. -/
theorem administration_spec {n : ℕ} (before comparator tree : BST 0 n) (H : ℕ)
    (oldHeight : ∀ record : External n, before.externalDepth record.val ≤ H)
    (height : ∀ record : External n, comparator.externalDepth record.val ≤ H)
    (reader : ℕ → HeapSides n → External n → External n → Entry)
    (readerKey : ∀ stage states record owner, (reader stage states record owner).key = record.val)
    (ports : List (External n)) (stage start : ℕ) (old prepared : HeapSides n)
    (free : ∀ record, record ∉ ports →
      labels comparator (contractedGap H)
        (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start prepared).states record ≤
          labels before (contractedGap H) old record)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels before (contractedGap H) old) :
    let actions := administration comparator tree (contractedGap H) reader ports stage start prepared
    let result := freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start prepared
    EntryJournal.Valid (contractedGap H) state actions ∧
      (run state actions).label = labels comparator (contractedGap H) result.states ∧
      total ordinary state actions ≤ ports.length ∧
      total positiveChange state actions ≤ 2 * ((contractedGap H : ℤ) - 1) * ports.length := by
  classical
  let target := labels comparator (contractedGap H) prepared
  let batched := run state (batch target)
  have newBound : ∀ record, 1 ≤ target record ∧ target record ≤ (contractedGap H : ℤ) :=
    fun record => label_bounded _ H prepared record (height record)
  have oldBound : Bounded (contractedGap H) state := by
    intro record
    rw [agree]
    exact label_bounded _ H old record (oldHeight record)
  have batchFree : ∀ record, record ∉ ports.toFinset → target record ≤ state.label record := by
    intro record outside
    rw [agree]
    have absent : record ∉ ports := by simpa using outside
    have unchanged := restore_labels_outside comparator tree (contractedGap H) reader readerKey ports stage start prepared record absent
    exact (le_of_eq unchanged.symm).trans (free record absent)
  have batchBound := batch_positive_le_ports (contractedGap H) state target ports.toFinset oldBound newBound batchFree
  have zero := relabel_zero ordinary (by intros; rfl) state target Finset.univ.toList
  change total ordinary state (batch target) = 0 at zero
  have tail := program_spec comparator tree H height reader readerKey ports stage start prepared batched
    (congrArg WeightedMemory.State.label (run_batch state target))
  dsimp only
  simp only [administration, valid_append, run_append, total_append]
  refine ⟨⟨batch_valid _ state target newBound, tail.1⟩, tail.2.1, ?_, ?_⟩
  · change total ordinary state (batch target) + _ ≤ _
    rw [zero, zero_add]
    exact tail.2.2.1
  · have size : (ports.toFinset.card : ℤ) ≤ ports.length := by exact_mod_cast List.toFinset_card_le ports
    have cap : 0 ≤ (contractedGap H : ℤ) - 1 := by unfold contractedGap; omega
    nlinarith [tail.2.2.2]

/-- The immutable entry returned by the fresh allocator records the same
labels used by its journal entry, at the actual pre-insertion state. -/
theorem stored_snapshot {n : ℕ} (comparator tree : BST 0 n) (K : ℤ) (clock : ℕ)
    (ports : List (External n)) (stage start : ℕ) (states : HeapSides n)
    (index : ℕ) (inside : index < ports.length) (record owner : External n) :
    let reader := Execution.entryReader comparator K clock
    let result := freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states
    let current := restorationState (Snapshot.ofTree comparator) tree reader ports stage start states index
    let entry := result.makeEntry (stage+index) record owner
    entry.entryLabel = labels comparator K current record ∧
      entry.creatorLabel = labels comparator K current owner := by
  dsimp only
  rw [freshRestorePorts_reader_at _ _ _ _ _ _ _ _ inside]
  exact ⟨rfl, rfl⟩

end Greedy.RestorationJournal
