import Greedy.JournalKinds
import Greedy.RunJournal

/-!
# Initial memberships in the chronological journal

Every nonroot record enters its actual initial parent's grower once.
Labels stay fixed, while the saved creator memory becomes exactly the
creator snapshot stored in the initial block state. Initial entries cost
at most one ordinary entry per external record.
-/

namespace Greedy.InitialJournal

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical Splay.Analysis
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives
open EntryJournal
open WeightedMemory (State)

variable {Record : Type*} [Fintype Record] [DecidableEq Record]

def install (parent : Record → Option Record) : List Record → List (Action Record)
  | [] => []
  | record :: rest =>
      (match parent record with
       | none => []
       | some owner => [.entry record owner .ordinary]) ++ install parent rest

theorem run_install (parent : Record → Option Record) (records : List Record) (state : State Record) :
    run state (install parent records) =
      ⟨state.label, fun record => if record ∈ records then
        match parent record with
        | none => state.memory record
        | some owner => state.label owner
        else state.memory record⟩ := by
  induction records generalizing state with
  | nil => simp [install, run]
  | cons record rest ih =>
      cases relation : parent record with
      | none =>
          simp only [install, relation, List.nil_append, ih]
          congr 1
          funext key
          by_cases same : key = record <;> by_cases member : key ∈ rest <;> simp [same, member, relation]
      | some owner =>
          simp only [install, relation, List.singleton_append, run, ih]
          change (⟨state.label, _⟩ : State Record) = ⟨state.label, _⟩
          congr 1
          funext key
          by_cases same : key = record <;> by_cases member : key ∈ rest <;>
            simp [step, encode, WeightedMemory.step, same, member, relation]

theorem install_ordinary (parent : Record → Option Record) (records : List Record) : OrdinaryOnly (install parent records) := by
  induction records with
  | nil => simp [OrdinaryOnly, install]
  | cons record rest ih =>
      cases relation : parent record <;> simp [install, relation, OrdinaryOnly, IsOrdinary, ih] at ⊢
      all_goals exact ih

theorem install_valid (parent : Record → Option Record) (records : List Record) (K : ℤ) (state : State Record) :
    EntryJournal.Valid K state (install parent records) := by
  induction records generalizing state with
  | nil => trivial
  | cons record rest ih =>
      cases relation : parent record with
      | none => simpa [install, relation] using ih state
      | some owner =>
          simp only [install, relation, List.singleton_append, EntryJournal.Valid]
          exact ⟨by simp [legal], ih (step state (.entry record owner .ordinary))⟩

theorem install_count (parent : Record → Option Record) (records : List Record) (state : State Record) :
    total ordinary state (install parent records) ≤ records.length := by
  induction records generalizing state with
  | nil => simp [install, total]
  | cons record rest ih =>
      cases relation : parent record with
      | none => simpa [install, relation] using (ih state).trans (by omega)
      | some owner =>
          have tail := ih (step state (.entry record owner .ordinary))
          simp only [install, relation, List.singleton_append, total, ordinary, List.length_cons, Nat.cast_add, Nat.cast_one]
          linarith

noncomputable def program {n : ℕ} (comparator tree : BST 0 n) : List (Action (External n)) :=
  install (canonicalParent (Snapshot.ofTree comparator) tree) Finset.univ.toList

theorem program_labels {n : ℕ} (comparator tree : BST 0 n) (state : State (External n)) :
    (run state (program comparator tree)).label = state.label := by
  rw [program, run_install]

theorem program_memory {n : ℕ} (comparator tree : BST 0 n) (state : State (External n))
    (record owner : External n) (parent : canonicalParent (Snapshot.ofTree comparator) tree record = some owner) :
    (run state (program comparator tree)).memory record = state.label owner := by
  rw [program, run_install]
  simp [parent]

theorem stored_memory {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (state : State (External n))
    (agree : state.label = RestorationJournal.labels comparator K (GreedyMerge.InitialBlocks.state (Snapshot.ofTree comparator) tree K))
    (owner record : External n) (side : Bool)
    (parent : canonicalParent (Snapshot.ofTree comparator) tree record = some owner) :
    (run state (program comparator tree)).memory record =
      (GreedyMerge.InitialBlocks.entry (Snapshot.ofTree comparator) tree K owner side record).creatorLabel := by
  rw [program_memory comparator tree state record owner parent, agree]
  exact (GreedyMerge.InitialBlocks.entry_snapshots comparator tree K owner record side).2.symm

end Greedy.InitialJournal
