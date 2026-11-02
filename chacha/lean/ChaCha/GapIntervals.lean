import ChaCha.CyclicRuns
import ChaCha.OccurrenceAccounting

/-!
# Chronological gap occurrence accounting

The cyclic direction identities use one gap between successive nontrivial runs
of a coarse cell. The retained record is valid on the open time interval between
two consecutive fine changes in that cell. This module proves that such open
intervals cannot charge the same occurrence, and constructs the direction gaps
from nonempty micro-step words.
-/

namespace ChaCha.GapIntervals

open CyclicRuns TurnAccounting

variable {Cell : Type*}

/-- A retained record's lifetime ends at the next fine change in its cell. -/
structure ConsecutiveChange (changes : Cell → ℕ → Prop) where
  cell : Cell
  start : ℕ
  finish : ℕ
  increasing : start < finish
  start_change : changes cell start
  finish_change : changes cell finish
  none_between : ∀ t, start < t → t < finish → ¬ changes cell t

/-- Two consecutive-change gaps of one cell containing one time are the same
chronological gap. This proves the delayed-payment injection from time order. -/
theorem same_interval_of_overlap {changes : Cell → ℕ → Prop}
    (g h : ConsecutiveChange changes) (same_cell : g.cell = h.cell) (t : ℕ)
    (gt : g.start < t ∧ t < g.finish) (ht : h.start < t ∧ t < h.finish) :
    g.start = h.start ∧ g.finish = h.finish := by
  have hs : g.start = h.start := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hm : h.start < g.finish := lt_trans ht.1 gt.2
      exact g.none_between h.start hlt hm (same_cell ▸ h.start_change)
    · have hm : g.start < h.finish := lt_trans gt.1 ht.2
      exact h.none_between g.start hgt hm (same_cell ▸ g.start_change)
  have he : g.finish = h.finish := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact h.none_between g.finish (by omega) hlt (same_cell ▸ g.finish_change)
    · exact g.none_between h.finish (by omega) hgt (same_cell ▸ h.finish_change)
  exact ⟨hs, he⟩

/-- Any chosen trigger inside each record lifetime determines its complete gap
uniquely from the pair `(coarse cell, trigger time)`. -/
theorem trigger_assignment_injective {I : Type*} {changes : Cell → ℕ → Prop}
    (gap : I → ConsecutiveChange changes)
    (indices : Function.Injective (fun i => ((gap i).cell, (gap i).start, (gap i).finish)))
    (trigger : I → ℕ)
    (inside : ∀ i, (gap i).start < trigger i ∧ trigger i < (gap i).finish) :
    Function.Injective (fun i => ((gap i).cell, trigger i)) := by
  intro i j hij
  have hc : (gap i).cell = (gap j).cell := congrArg Prod.fst hij
  have ht : trigger i = trigger j := congrArg Prod.snd hij
  have hh := same_interval_of_overlap (gap i) (gap j) hc (trigger i)
    (inside i) (by simpa only [ht] using inside j)
  apply indices
  simp only [Prod.mk.injEq]
  exact ⟨hc, hh.1, hh.2⟩

/-- A nontrivial coarse run has a nonempty actual micro direction word. The
outside-side list is the chronological excursion since the preceding such run. -/
structure MicroRun where
  steps : Block Bool
  outsideBefore : List Bool

def gapsFrom : Bool → List MicroRun → List Gap
  | _, [] => []
  | previous, r :: rs =>
      { previousMicro := previous, nextMicro := r.steps.first,
        outsideSides := r.outsideBefore } :: gapsFrom r.steps.last rs

def microWords (rs : List MicroRun) : List (List Bool) := rs.map (fun r => r.steps.word)

def cycleGaps (rs : List MicroRun) : List Gap :=
  gapsFrom ((microWords rs).flatten.getLastD false) rs

theorem gapsFrom_length (previous : Bool) (rs : List MicroRun) :
    (gapsFrom previous rs).length = rs.length := by
  induction rs generalizing previous with
  | nil => rfl
  | cons r rs ih => simp [gapsFrom, ih]

theorem gapsFrom_join (previous : Bool) (rs : List MicroRun) :
    ((gapsFrom previous rs).map Gap.join).sum = joinsFrom previous (microWords rs) := by
  induction rs generalizing previous with
  | nil => rfl
  | cons r rs ih =>
    simp only [gapsFrom, List.map_cons, List.sum_cons, Gap.join, microWords, Block.word,
      joinsFrom, Block.last]
    exact congrArg (fun k => turn previous r.steps.first + k) (ih r.steps.last)

/-- Micro join turns are counted exactly by the constructed gaps. -/
theorem cycleGaps_join (rs : List MicroRun) :
    ((cycleGaps rs).map Gap.join).sum = cyclicJoins (microWords rs) :=
  gapsFrom_join _ _

def MicroRun.entry (r : MicroRun) : ℕ :=
  turn (!r.outsideBefore.getLastD r.steps.first) r.steps.first

/-- The default in `Gap.entry` is irrelevant for a genuine nonempty excursion. -/
theorem gap_entry_of_nonempty (previous : Bool) (r : MicroRun)
    (outside : r.outsideBefore ≠ []) :
    (Gap.mk previous r.steps.first r.outsideBefore).entry = r.entry := by
  cases h : r.outsideBefore with
  | nil => exact False.elim (outside h)
  | cons a as => simp only [Gap.entry, MicroRun.entry, h, List.getLastD_cons]

theorem gapsFrom_entry (previous : Bool) (rs : List MicroRun)
    (outside : ∀ r ∈ rs, r.outsideBefore ≠ []) :
    ((gapsFrom previous rs).map Gap.entry).sum = (rs.map MicroRun.entry).sum := by
  induction rs generalizing previous with
  | nil => rfl
  | cons r rs ih =>
    have hr := outside r (by simp)
    have hrs : ∀ s ∈ rs, s.outsideBefore ≠ [] := fun s hs => outside s (by simp [hs])
    simp only [gapsFrom, List.map_cons, List.sum_cons]
    rw [gap_entry_of_nonempty previous r hr, ih r.steps.last hrs]

/-- One genuine demand per nontrivial run is paid by an actual excursion
reversal, an entry direction change, or a counted micro join. -/
theorem micro_cycle_gap_cover (rs : List MicroRun)
    (outside : ∀ r ∈ rs, r.outsideBefore ≠ []) :
    rs.length ≤ ((cycleGaps rs).map Gap.delayed).sum +
      (rs.map MicroRun.entry).sum + cyclicJoins (microWords rs) := by
  have hg := gaps_cover (cycleGaps rs)
  rw [cycleGaps_join] at hg
  unfold cycleGaps at hg
  rw [gapsFrom_length, gapsFrom_entry _ rs outside] at hg
  exact hg

end ChaCha.GapIntervals
