import Greedy.HistoryState
import Greedy.GrowthAccessInvariant

/-! Timestamped label history for literal consolidation links. -/

namespace Greedy.LabelSnapshots

open Splay.Tree Splay.Tree.BST Splay.Rank Splay.Lazy.Canonical
open GreedyMerge.OrderedBlocks GreedyMerge.Primitives GreedyMerge.ActualLinks

noncomputable def accessHistory {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool) :
    ℕ → States n → List (External n × External n) → LabelHistory.History (External n) → LabelHistory.History (External n)
  | _, _, [], history => history
  | clock, states, event :: rest, history =>
      let entry := arrivalEntry (GreedyMerge.StateLabels.label comparator.externalDepth K states) event.1 event.2 clock
      let next := linkState states source event.1 event.2 (sourceSide event) (targetSide event) entry
      accessHistory comparator K source sourceSide (clock+1) next rest
        (LabelHistory.update history clock (RestorationJournal.labels comparator K next))

theorem linkState_creators {n : ℕ} (states : States n) (source winner loser : External n)
    (sourceSide targetSide : Bool) (entry : Entry) (creators : GrowthJournal.Creators states) :
    GrowthJournal.Creators (linkState states source winner loser sourceSide targetSide entry) := by
  intro owner side grower present
  unfold linkState at present
  split_ifs at present
  · exact GrowthJournal.append_creator owner.val entry (states owner side) (creators owner side) grower present
  · exact creators owner side grower present
  · exact creators owner side grower present

theorem access_sound {n : ℕ} (comparator : BST 0 n) (K : ℤ)
    (source : External n) (sourceSide : External n × External n → Bool)
    (clock : ℕ) (states : States n) (events : List (External n × External n))
    (history : LabelHistory.History (External n)) (sound : Sound comparator K clock states history)
    (before : BeforeTime clock states) (creators : GrowthJournal.Creators states) :
    let result := runLinks source sourceSide (fun _ current => GreedyMerge.StateLabels.label comparator.externalDepth K current)
      clock states events
    Sound comparator K (clock+events.length) result (accessHistory comparator K source sourceSide clock states events history) ∧
      BeforeTime (clock+events.length) result ∧ GrowthJournal.Creators result := by
  induction events generalizing clock states history with
  | nil => simpa only [runLinks, accessHistory, List.length_nil, Nat.add_zero] using And.intro sound (And.intro before creators)
  | cons event rest ih =>
      let entry := arrivalEntry (GreedyMerge.StateLabels.label comparator.externalDepth K states) event.1 event.2 clock
      let next := linkState states source event.1 event.2 (sourceSide event) (targetSide event) entry
      have fresh : Snapshot history event.1.val entry :=
        reader_snapshot comparator K history clock states sound.before sound.current event.2 event.1
      have temporal := linkState_time states source event.1 event.2 (sourceSide event) (targetSide event) entry rfl creators before
      have preserved := linkState_snapshots states source event.1 event.2 (sourceSide event) (targetSide event) entry sound.snapshots creators fresh
      have nextCreators := linkState_creators states source event.1 event.2 (sourceSide event) (targetSide event) entry creators
      have tail := ih (clock+1) next (LabelHistory.update history clock (RestorationJournal.labels comparator K next))
        (sound.update preserved temporal) temporal nextCreators
      simpa only [runLinks, accessHistory, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using tail

end Greedy.LabelSnapshots
