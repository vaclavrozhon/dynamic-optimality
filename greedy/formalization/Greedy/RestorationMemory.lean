import Greedy.LiveMemory

/-! Exact latest-entry memories through sequential paid restorations. -/

namespace Greedy.LiveMemory

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation EntryJournal RestorationJournal

theorem one_labels {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : States n) (state : WeightedMemory.State (External n))
    (agree : state.label = labels comparator K states) :
    (run state (one comparator tree K names makeEntry record states)).label =
      labels comparator K (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1 := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simpa only [one, restorePort, parent, run] using agree
  | some owner => simp only [one, parent, run, run_batch]

theorem restoration {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (keys : ∀ stage current record owner, (reader stage current record owner).key = record.val)
    (snapshots : ∀ stage current record owner,
      (reader stage current record owner).creatorLabel = labels comparator K current owner)
    (ports : List (External n)) (distinct : ports.Nodup) (stage start : ℕ)
    (states : States n) (ordered : Ordered states)
    (absent : ∀ record ∈ ports, ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (state : WeightedMemory.State (External n)) (agree : state.label = labels comparator K states)
    (synced : Synced state.memory states) :
    Synced (run state (program comparator tree K reader ports stage start states)).memory
      (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states ∧
    (run state (program comparator tree K reader ports stage start states)).label =
      labels comparator K (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states ∧
    Ordered (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states := by
  induction ports generalizing stage start states state with
  | nil => exact ⟨synced, agree, ordered⟩
  | cons record rest ih =>
      let names := portNames (Snapshot.ofTree comparator) tree record start states
      let head := restorePort (Snapshot.ofTree comparator) tree names (reader stage states record) record states
      let actions := one comparator tree K names (reader stage states record) record states
      have headSynced := restore comparator tree K names (reader stage states record) record states state agree synced
        (absent record (by simp)) (keys stage states record) (snapshots stage states record)
      have headLabels := one_labels comparator tree K names (reader stage states record) record states state agree
      have headOrdered := restorePort_valid (Snapshot.ofTree comparator) tree names (reader stage states record)
        record states ordered (keys stage states record) (absent record (by simp))
      have tailAbsent : ∀ other ∈ rest, ¬ GreedyMerge.BlockCoverage.Represented head.1 other.val := by
        intro other member represented
        rcases (restorePort_represented (Snapshot.ofTree comparator) tree names (reader stage states record)
          record states ordered (keys stage states record) other.val).mp represented with previous | ⟨same, _⟩
        · exact absent other (by simp [member]) previous
        · have equal : other = record := Fin.ext same
          exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
      have tail := ih (List.nodup_cons.mp distinct).2 (stage+1)
        (restoreNext (Snapshot.ofTree comparator) tree record start states) head.1 headOrdered tailAbsent
        (run state actions) headLabels headSynced
      simpa only [program, run_append, freshRestorePorts] using tail

theorem administration {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (reader : ℕ → States n → External n → External n → Entry)
    (keys : ∀ stage current record owner, (reader stage current record owner).key = record.val)
    (snapshots : ∀ stage current record owner,
      (reader stage current record owner).creatorLabel = labels comparator K current owner)
    (ports : List (External n)) (distinct : ports.Nodup) (stage start : ℕ)
    (states : States n) (ordered : Ordered states)
    (absent : ∀ record ∈ ports, ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (state : WeightedMemory.State (External n)) (synced : Synced state.memory states) :
    Synced (run state (RestorationJournal.administration comparator tree K reader ports stage start states)).memory
      (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states ∧
    Ordered (freshRestorePorts (Snapshot.ofTree comparator) tree reader ports stage start states).states := by
  rw [RestorationJournal.administration, run_append, run_batch]
  have result := restoration comparator tree K reader keys snapshots ports distinct stage start states ordered absent
    ⟨labels comparator K states, state.memory⟩ rfl synced
  exact ⟨result.1, result.2.2⟩

end Greedy.LiveMemory
