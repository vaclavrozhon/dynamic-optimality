import LabelTimeline
import ActualLinkClasses

/-!
The validated timeline of an actual stable-link run. Good marks use
frozen source snapshots; their equality with actual link snapshots is
proved by permanent loser removal. No local drop or update-value bound
is supplied separately for each event.
-/
namespace GreedyForest.Phase

open Splay.Analysis
open GreedyMerge.Fringe.Schedule

def timelineUpdate (rank block : ℕ → ℕ) (frozen : ℕ → ℤ) (event : ℕ × ℕ) :
    Timeline.Update ℕ ℕ where
  record := event.2
  value := contractedGap (rank event.2-rank event.1)
  origin := .phase (block event.2)
  good := decide (block event.1=block event.2 ∧ frozen event.1=frozen event.2)

theorem timeline_apply_eq (rank block : ℕ → ℕ) (frozen labels : ℕ → ℤ)
    (event : ℕ × ℕ) :
    Timeline.applyUpdate labels (timelineUpdate rank block frozen event) =
      linkLabels rank labels event := rfl

theorem timeline_run_eq (rank block : ℕ → ℕ) (frozen labels : ℕ → ℤ)
    (events : List (ℕ × ℕ)) :
    Timeline.run labels (events.map (timelineUpdate rank block frozen)) =
      runLabels rank labels events := by
  induction events generalizing labels with
  | nil => rfl
  | cons event events ih =>
      exact ih (linkLabels rank labels event)

theorem timeline_snapshot_eq (rank block : ℕ → ℕ) (frozen labels : ℕ → ℤ)
    (events : List (ℕ × ℕ)) (time : ℕ) :
    Timeline.stateAt labels (events.map (timelineUpdate rank block frozen)) time =
      labelsAt rank labels events time := by
  simp only [Timeline.stateAt,←List.map_take]
  exact timeline_run_eq rank block frozen labels (events.take time)

/-- The invariant needed for induction is that all current roots retain
their initial source snapshot, regardless of labels of departed records. -/
theorem timeline_valid_of_source_snapshots {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup)
    (labels frozen : ℕ → ℤ) (block base : ℕ → ℕ) (H : ℕ)
    (hfreeze : ∀ v ∈ before, labels v=frozen v)
    (hb : ∀ v ∈ before, frozen v=baseLabel rank (base (block v)) v)
    (hf : ∀ v ∈ before, base (block v)≤rank v)
    (hrank : ∀ v ∈ before, rank v≤H) :
    Timeline.Valid (contractedGap H) labels (events.map (timelineUpdate rank block frozen)) := by
  induction hrun generalizing labels with
  | nil roots => trivial
  | @cons event events before middle after first rest ih =>
      have hm := first.members
      have hnew : (1:ℤ) ≤ contractedGap (rank event.2-rank event.1) ∧
          (contractedGap (rank event.2-rank event.1):ℤ) ≤ contractedGap H := by
        constructor
        · simp only [contractedGap]; omega
        · have h := contractedGap_mono
            (show rank event.2-rank event.1 ≤ H by have := hrank _ hm.2; omega)
          exact_mod_cast h
      refine ⟨⟨hnew,?_,?_⟩,?_⟩
      · intro hfree
        cases hfree
      · intro hgood
        have hg : block event.1=block event.2 ∧ frozen event.1=frozen event.2 := by
          simpa only [timelineUpdate,decide_eq_true_eq] using hgood
        have hw := (hfreeze _ hm.1).trans (hb _ hm.1)
        have hl := (hfreeze _ hm.2).trans (hb _ hm.2)
        rw [←hg.1] at hl
        have heq : labels event.1=labels event.2 := by
          rw [hfreeze _ hm.1,hfreeze _ hm.2]
          exact hg.2
        have hd := good_link_drop first labels (base (block event.1))
          (hf _ hm.1) hw hl heq
        simp only [linkLabels,Function.update_self] at hd
        change (contractedGap (rank event.2-rank event.1):ℤ)+1 ≤ labels event.2
        omega
      · apply ih (hn.sublist first.sublist) (linkLabels rank labels event)
        · intro v hv
          exact (link_survivor_labels first hn labels v hv).trans
            (hfreeze v (first.sublist.subset hv))
        · intro v hv; exact hb v (first.sublist.subset hv)
        · intro v hv; exact hf v (first.sublist.subset hv)
        · intro v hv; exact hrank v (first.sublist.subset hv)

/-- A whole actual phase is a valid composable label timeline. Its
positive and good-cell properties follow from LabelTimeline without
supplying aggregate variation, individual drop, or paid-slot witnesses. -/
theorem actual_phase_timeline_valid {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup)
    (initial : ℕ → ℤ) (block base : ℕ → ℕ) (H : ℕ)
    (hb : ∀ v ∈ before, initial v=baseLabel rank (base (block v)) v)
    (hf : ∀ v ∈ before, base (block v)≤rank v)
    (hrank : ∀ v ∈ before, rank v≤H) :
    Timeline.Valid (contractedGap H) initial (events.map (timelineUpdate rank block initial)) := by
  exact timeline_valid_of_source_snapshots hrun hn initial initial block base H
    (fun _ _ => rfl) hb hf hrank

/-- The timeline's static good mark identifies exactly the actual
same-source/equal-snapshot link classification at that occurrence. -/
theorem timeline_good_iff_actual {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (hrun : Run rank events before after) (hn : before.Nodup)
    (initial : ℕ → ℤ) (block : ℕ → ℕ) (i : Fin events.length) :
    (timelineUpdate rank block initial (events.get i)).good = true ↔
      i ∈ actualInternalGood rank initial events block := by
  classical
  have hs := actual_event_source_labels hrun hn initial i
  simp only [timelineUpdate,decide_eq_true_eq,actualInternalGood,
    Finset.mem_filter,Finset.mem_univ,true_and,hs.1,hs.2]

end GreedyForest.Phase

#print axioms GreedyForest.Phase.actual_phase_timeline_valid
#print axioms GreedyForest.Phase.timeline_snapshot_eq
#print axioms GreedyForest.Phase.timeline_good_iff_actual
