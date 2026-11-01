import Greedy.EntryProperties
import Greedy.InitialJournal

/-! Live memberships retain exactly the journal's latest creator memory. -/

namespace Greedy.LiveMemory

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation EntryJournal RestorationJournal

def Synced {n : ℕ} (memory : External n → ℤ) (states : States n) : Prop :=
  EntryProperties.Held (fun entry _ => ∀ record : External n,
    record.val = entry.key → memory record = entry.creatorLabel) states

theorem Synced.entry {n : ℕ} {memory : External n → ℤ} {states : States n}
    (synced : Synced memory states) (owner : External n) (side : Bool)
    (entry : Entry) (member : entry ∈ entries (states owner side))
    (record : External n) (key : record.val = entry.key) : memory record = entry.creatorLabel := by
  obtain ⟨creator, tagged⟩ := EntryProperties.entry_tagged _ entry member
  exact synced owner side entry creator tagged record key

theorem initial {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (state : WeightedMemory.State (External n))
    (agree : state.label = labels comparator K (GreedyMerge.InitialBlocks.state (Snapshot.ofTree comparator) tree K)) :
    Synced (run state (InitialJournal.program comparator tree)).memory
      (GreedyMerge.InitialBlocks.state (Snapshot.ofTree comparator) tree K) := by
  intro owner side item creator member record key
  have actual := EntryProperties.tagged_entry _ item creator member
  rw [GreedyMerge.InitialBlocks.state_entries] at actual
  obtain ⟨original, child, rfl⟩ := List.mem_map.mp actual
  have same : record = original := Fin.ext key
  subst record
  have parent := (GreedyMerge.InitialBlocks.mem_children ..).mp child
  exact InitialJournal.stored_memory comparator tree K state agree owner original side parent.1

theorem restore {n : ℕ} (comparator tree : BST 0 n) (K : ℤ)
    (names : PaidNames) (makeEntry : External n → Entry) (record : External n)
    (states : States n) (state : WeightedMemory.State (External n))
    (agree : state.label = labels comparator K states)
    (synced : Synced state.memory states)
    (absent : ¬ GreedyMerge.BlockCoverage.Represented states record.val)
    (keys : ∀ owner, (makeEntry owner).key = record.val)
    (snapshots : ∀ owner, (makeEntry owner).creatorLabel = labels comparator K states owner) :
    Synced (run state (one comparator tree K names makeEntry record states)).memory
      (restorePort (Snapshot.ofTree comparator) tree names makeEntry record states).1 := by
  cases parent : canonicalParent (Snapshot.ofTree comparator) tree record with
  | none => simpa only [one, restorePort, parent, run] using synced
  | some owner =>
      have memory : (run state (one comparator tree K names makeEntry record states)).memory =
          Function.update state.memory record (state.label owner) := by
        simp only [one, parent, run, run_batch]
        rfl
      rw [memory]
      have old : Synced (Function.update state.memory record (state.label owner)) states := by
        intro place side item creator member query key
        have different : query ≠ record := by
          intro equal
          apply absent
          exact ⟨place, side, item, EntryProperties.tagged_entry _ item creator member, key.symm.trans (congrArg Fin.val equal)⟩
        rw [Function.update_of_ne different]
        exact synced place side item creator member query key
      intro place side item creator member query key
      simp only [restorePort, parent, replaceSide] at member
      split_ifs at member with selected
      · obtain ⟨placeEq, sideEq⟩ := selected
        subst place
        subst side
        rcases LabelSnapshots.tagged_installPaid owner.val _ _ _ _ _ _ _ item creator member with previous | ⟨rfl, rfl⟩
        · exact old owner _ item creator (by simpa using previous) query key
        · have same : query = record := Fin.ext (key.trans (keys owner))
          subst query
          rw [Function.update_self, snapshots, agree]
      · exact old place side item creator member query key

end Greedy.LiveMemory
