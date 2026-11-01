import Greedy.RunLabelHistory
import Greedy.RunJournal

/-! One final label history validates the stored sources of every access. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks
open GreedyMerge.HeapAllocation GreedyMerge.GrowthBook

def AllSourcesSnapshots {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (history : LabelHistory.History (External n)) : Execution.Run K first last requests → Prop
  | .done state => HeapSnapshots history state.blocks
  | .rotate (first := first) _ _ _ rest => HeapSnapshots history first.blocks ∧ AllSourcesSnapshots history rest
  | .access (first := first) request _ _ _ _ rest =>
      HeapSnapshots history first.blocks ∧ HeapSnapshots history (RunJournal.prepared first request) ∧ AllSourcesSnapshots history rest

theorem all_sources_snapshots {n : ℕ} {K : ℤ} {first last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K first last requests) (valid : first.Valid)
    (books : HeapBooks n) (growth : GrowthJournal.Invariant first.clock first.next first.blocks books)
    (history : LabelHistory.History (External n)) (sound : Sound first.comparator K first.clock first.blocks history) :
    ∃ finalHistory, Sound last.comparator K last.clock last.blocks finalHistory ∧
      LabelHistory.Future history finalHistory first.clock ∧ AllSourcesSnapshots finalHistory execution := by
  induction execution generalizing books history with
  | done => exact ⟨history, sound, .refl _ _, sound.snapshots⟩
  | @rotate first last after depth requests rotation data afterValid rest ih =>
      obtain ⟨nextHistory, nextSound, head, advance⟩ := complete_rotation_sound first after rotation K data history sound valid.2.1
      obtain ⟨nextBooks, nextGrowth, _⟩ := GrowthJournal.complete_rotation_history first after rotation K data books growth
      obtain ⟨finalHistory, finalSound, tail, sources⟩ := ih afterValid nextBooks nextGrowth nextHistory nextSound
      have extension := head.trans (tail.weaken first.clock advance)
      have time := ((chronology_iff ..).mp (valid.2.1.mono (Nat.le_succ first.clock))).2
      exact ⟨finalHistory, finalSound, extension, sound.snapshots.future extension time, sources⟩
  | @access first last requests request root decomposition data afterValid rest ih =>
      obtain ⟨nextHistory, nextSound, head⟩ := afterAccess_sound first request K decomposition data history sound
        ((chronology_iff ..).mp valid.2.1).2 growth.creators
      obtain ⟨nextBooks, nextGrowth, _⟩ := GrowthJournal.access_history first request K decomposition data books growth
      obtain ⟨finalHistory, finalSound, tail, sources⟩ := ih afterValid nextBooks nextGrowth nextHistory nextSound
      have advance : first.clock ≤ (Execution.afterAccess first request K decomposition data).clock := Nat.le_add_right _ _
      have extension := head.trans (tail.weaken first.clock advance)
      have time := ((chronology_iff ..).mp (valid.2.1.mono (Nat.le_succ first.clock))).2
      have snapshots := sound.snapshots.future extension time
      exact ⟨finalHistory, finalSound, extension, snapshots,
        convertHeap_snapshots _ _ first.next first.blocks snapshots, sources⟩

theorem initialized_all_snapshots {n : ℕ} (initial comparator : BST 0 n) (K : ℤ)
    {last : Execution.State n} {requests : List (Fin n)}
    (execution : Execution.Run K (Execution.initial initial comparator K) last requests) :
    ∃ history, Sound last.comparator K last.clock last.blocks history ∧ AllSourcesSnapshots history execution := by
  obtain ⟨history, sound, _, sources⟩ := all_sources_snapshots execution (Execution.initial_valid initial comparator K)
    (GreedyMerge.GrowthBook.initial (Splay.Rank.Snapshot.ofTree comparator) (Execution.initial initial comparator K).refined.tree K)
    (GrowthJournal.initial_invariant (Splay.Rank.Snapshot.ofTree comparator) _ K) _ (initial_sound comparator _ K)
  exact ⟨history, sound, sources⟩

end Greedy.LabelSnapshots
