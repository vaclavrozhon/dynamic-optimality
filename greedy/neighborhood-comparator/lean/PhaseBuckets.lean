import FringeSchedule
import Splay.Analysis.ContractedGap

/-!
Actual elementary label updates along the proved adjacent-root schedule.
At the start of a phase each source record has a frozen base. Linking
changes only the removed loser's label to its gap from the winner; hence
all current roots retain their original source labels until departure.
-/
namespace GreedyForest.Phase

open GreedyMerge.Fringe.Schedule
open Splay.Analysis

def baseLabel (rank : ℕ → ℕ) (base key : ℕ) : ℤ :=
  contractedGap (rank key - base)

def linkLabels (rank : ℕ → ℕ) (labels : ℕ → ℤ) (event : ℕ × ℕ) : ℕ → ℤ :=
  Function.update labels event.2 (contractedGap (rank event.2 - rank event.1))

def runLabels (rank : ℕ → ℕ) (labels : ℕ → ℤ) (events : List (ℕ × ℕ)) : ℕ → ℤ :=
  events.foldl (linkLabels rank) labels

theorem link_rank_order {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) : rank event.1 < rank event.2 := by
  cases h <;> assumption

theorem link_length {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) : before.length = after.length + 1 := by
  cases h <;> simp <;> omega

/-- Exact root-count conservation for the actual stable-link run. -/
theorem run_length {rank : ℕ → ℕ} {events : List (ℕ × ℕ)} {before after : List ℕ}
    (h : Run rank events before after) : before.length = events.length + after.length := by
  induction h with
  | nil roots => simp
  | cons first rest ih =>
      have hl := link_length first
      simp only [List.length_cons]
      omega

theorem run_losers_nodup {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (h : Run rank events before after) (hn : before.Nodup) :
    (events.map Prod.snd).Nodup := by
  induction h with
  | nil roots => simp
  | @cons event events before middle after first rest ih =>
      simp only [List.map_cons,List.nodup_cons]
      refine ⟨?_,ih (hn.sublist first.sublist)⟩
      intro hm
      obtain ⟨later,hlater,heq⟩ := List.mem_map.mp hm
      exact (loser_never_used_again first rest hn later hlater).2 heq

theorem run_events_nodup {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (h : Run rank events before after) (hn : before.Nodup) :
    events.Nodup := by
  exact (run_losers_nodup h hn).of_map

theorem link_survivor_labels {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) (hn : before.Nodup) (labels : ℕ → ℤ)
    (v : ℕ) (hv : v ∈ after) : linkLabels rank labels event v = labels v := by
  have hne : v ≠ event.2 := by
    intro heq
    subst v
    exact h.loser_absent hn hv
  simp [linkLabels, hne]

/-- This is a property of the actual stable-link execution, not an
assumed source-label invariant. Every surviving root keeps its entry
phase label through an arbitrary prefix of the execution. -/
theorem run_survivor_labels {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before after : List ℕ} (h : Run rank events before after)
    (hn : before.Nodup) (labels : ℕ → ℤ) (v : ℕ) (hv : v ∈ after) :
    runLabels rank labels events v = labels v := by
  induction h generalizing labels with
  | nil roots => rfl
  | @cons event events before middle after first rest ih =>
      have hm : middle.Nodup := hn.sublist first.sublist
      have hvm : v ∈ middle := rest.sublist.subset hv
      have ht := ih hm (linkLabels rank labels event) hv
      change runLabels rank (linkLabels rank labels event) events v = labels v
      rw [ht]
      exact link_survivor_labels first hn labels v hvm

theorem run_current_root_bucket {rank : ℕ → ℕ} {events : List (ℕ × ℕ)}
    {before current : List ℕ} (h : Run rank events before current)
    (hn : before.Nodup) (labels : ℕ → ℤ) (base : ℕ → ℕ)
    (hb : ∀ v ∈ before, labels v = baseLabel rank (base v) v)
    (v : ℕ) (hv : v ∈ current) :
    runLabels rank labels events v = baseLabel rank (base v) v := by
  rw [run_survivor_labels h hn labels v hv]
  exact hb v (h.sublist.subset hv)

/-- Equal buckets of actual same-base roots produce a genuine unit
decrease at the loser's actual label-update cell. -/
theorem good_link_drop {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) (labels : ℕ → ℤ) (base : ℕ)
    (hfloor : base ≤ rank event.1)
    (hw : labels event.1 = baseLabel rank base event.1)
    (hl : labels event.2 = baseLabel rank base event.2)
    (heq : labels event.1 = labels event.2) :
    linkLabels rank labels event event.2 - labels event.2 ≤ -1 := by
  have hr := link_rank_order h
  have hb := internalPairingGap_of_ranks (ownerRank:=base) (intervalGap:=0) hfloor hr
  dsimp at hb
  have heq' : contractedGap (rank event.1-base) = contractedGap (rank event.2-base) := by
    have he := hw.symm.trans (heq.trans hl)
    unfold baseLabel at he
    exact_mod_cast he
  have hd := hb.2 heq'
  have hd' : (contractedGap (rank event.2-rank event.1) : ℤ) + 1 ≤
      contractedGap (rank event.2-base) := by exact_mod_cast hd
  rw [hl]
  simp only [linkLabels, Function.update_self, baseLabel]
  omega

/-- Different buckets at a legal same-base link are strictly ordered.
Sampling the new membership before the loser update therefore gives
the positive entry-rank premise of the history ledger. -/
theorem bad_entry_strict {rank : ℕ → ℕ} {event : ℕ × ℕ} {before after : List ℕ}
    (h : Link rank event before after) (labels : ℕ → ℤ) (base : ℕ)
    (hw : labels event.1 = baseLabel rank base event.1)
    (hl : labels event.2 = baseLabel rank base event.2)
    (hne : labels event.1 ≠ labels event.2) : labels event.1 + 1 ≤ labels event.2 := by
  have hr := link_rank_order h
  have hm := contractedGap_mono (show rank event.1-base ≤ rank event.2-base by omega)
  have hmi : labels event.1 ≤ labels event.2 := by
    rw [hw, hl]
    unfold baseLabel
    exact_mod_cast hm
  omega

/-- A harmless boundary nondrop is necessarily a strict rise in the
common source-base labels. These are the labels counted on the geometric
cut path; the winner's own block label is deliberately irrelevant. -/
theorem boundary_nondrop_strict_rise {rank : ℕ → ℕ} {event : ℕ × ℕ}
    {before after : List ℕ} (h : Link rank event before after)
    (labels : ℕ → ℤ) (base : ℕ) (hfloor : base ≤ rank event.1)
    (hl : labels event.2 = baseLabel rank base event.2)
    (hnd : labels event.2 ≤ linkLabels rank labels event event.2) :
    baseLabel rank base event.1 < baseLabel rank base event.2 := by
  have hr := link_rank_order h
  have hm := contractedGap_mono (show rank event.1-base ≤ rank event.2-base by omega)
  have hm' : baseLabel rank base event.1 ≤ baseLabel rank base event.2 := by
    unfold baseLabel
    exact_mod_cast hm
  by_contra hnot
  have heq : baseLabel rank base event.1 = baseLabel rank base event.2 := by omega
  have hb := internalPairingGap_of_ranks (ownerRank:=base) (intervalGap:=0) hfloor hr
  dsimp at hb
  have heq' : contractedGap (rank event.1-base) = contractedGap (rank event.2-base) := by
    unfold baseLabel at heq
    exact_mod_cast heq
  have hd := hb.2 heq'
  rw [hl] at hnd
  simp only [linkLabels, Function.update_self, baseLabel] at hnd
  omega

end GreedyForest.Phase
