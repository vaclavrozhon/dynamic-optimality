import Greedy.AccessMemory
import Greedy.JournalLinkSums

/-! Unprocessed source endpoints retain their precise pre-phase creator memories. -/

namespace Greedy.AccessJournal

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.ActualLinks
open EntryJournal

theorem memory_unchanged {n : ℕ} (rank : ℕ → ℕ)
    (kind : External n × External n → Kind) (events : List (External n × External n))
    (state : WeightedMemory.State (External n)) (record : External n)
    (absent : record ∉ events.map Prod.snd) :
    (run state (program rank kind events)).memory record = state.memory record := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      have different : record ≠ event.2 := by intro same; exact absent (by simp [same])
      have tailAbsent : record ∉ rest.map Prod.snd := by intro member; exact absent (by simp [member])
      change (run (advance rank kind state event) (program rank kind rest)).memory record = _
      rw [ih _ tailAbsent]
      simp [advance, step, encode, WeightedMemory.step, Function.update_of_ne different]

open Splay.Tree GreedyMerge.PathPlateau GreedyMerge.AccessSourceAccounting

theorem source_memories {n access : ℕ} {comparator oldTree newTree : BST 0 n}
    {p : Decomposition oldTree access} (data : AccessScheduleData comparator oldTree newTree p)
    (source : External n) (geometry : AccessTrace.Geometry data source)
    (kind : External n × External n → Kind) (state : WeightedMemory.State (External n))
    (index : Fin data.events.length) :
    let current := run state (program comparator.externalDepth kind (data.events.take index.val))
    current.memory (data.events.get index).1 = state.memory (data.events.get index).1 ∧
    current.memory (data.events.get index).2 = state.memory (data.events.get index).2 := by
  obtain ⟨middle, firstRun, suffix⟩ := GreedyForest.Phase.run_take_split geometry.run index.val
    (by simpa only [List.length_map] using Nat.le_of_lt index.isLt)
  have member : eventKeys (data.events.get index) ∈ (data.events.map eventKeys).drop index.val := by
    rw [← List.map_drop]
    apply List.mem_map.mpr
    refine ⟨_, ?_, rfl⟩
    rw [List.drop_eq_getElem_cons index.isLt]
    exact List.mem_cons_self
  have endpoints := suffix.event_members _ member
  have unchanged (record : External n) (present : record.val ∈ middle) :
      (run state (program comparator.externalDepth kind (data.events.take index.val))).memory record = state.memory record := by
    apply memory_unchanged
    have neverLost := (GreedyMerge.HistoryProcess.run_survivor_iff firstRun geometry.unique record.val).mp present |>.2
    intro lost
    obtain ⟨event, eventMem, same⟩ := List.mem_map.mp lost
    apply neverLost
    rw [← List.map_take]
    exact List.mem_map.mpr ⟨eventKeys event, List.mem_map.mpr ⟨event, eventMem, rfl⟩, congrArg Fin.val same⟩
  exact ⟨unchanged _ endpoints.1, unchanged _ endpoints.2⟩

end Greedy.AccessJournal

namespace Greedy.LiveMemory

open Splay.Rank GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks

noncomputable def stored {n : ℕ} (states : States n) (record : External n) : ℤ := by
  classical
  exact if present : ∃ owner side entry, entry ∈ entries (states owner side) ∧ entry.key = record.val then
    present.choose_spec.choose_spec.choose.creatorLabel else 0

theorem stored_eq {n : ℕ} (states : States n) (record : External n) (memory : External n → ℤ)
    (synced : Synced memory states) (present : GreedyMerge.BlockCoverage.Represented states record.val) :
    stored states record = memory record := by
  classical
  change (∃ owner side entry, entry ∈ entries (states owner side) ∧ entry.key = record.val) at present
  simp only [stored, dif_pos present]
  exact (synced.entry present.choose present.choose_spec.choose present.choose_spec.choose_spec.choose
    present.choose_spec.choose_spec.choose_spec.1 record present.choose_spec.choose_spec.choose_spec.2.symm).symm

end Greedy.LiveMemory
