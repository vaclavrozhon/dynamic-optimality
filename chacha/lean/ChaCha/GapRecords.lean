import ChaCha.Witnesses

/-!
# From chronological run gaps to actual witness records

These constructors retain the global access decomposition, including requests
outside the gadget owner. A first opposite-side occurrence is selected from the
actual finite gap; its earlier prefix satisfies the delayed-record conditions.
-/

namespace ChaCha.Witnesses

open Primary

/-- A trigger leaves the retained coarse cell in the direction opposite its
source micro step. -/
def OppositeTrigger (q : Gadget) (source next target : Key) : Prop :=
  q.owner.IsPrefix target ∧ q.coarse target ≠ q.coarse source ∧
    ((target < source ∧ source < next) ∨ (next < source ∧ source < target))

/-- Every nonempty set of occurrences in a finite list has a first occurrence,
with its exact chronological prefix and suffix retained. -/
theorem first_hit_split {α : Type*} (P : α → Prop) [DecidablePred P]
    (xs : List α) (hit : ∃ x ∈ xs, P x) :
    ∃ before x after, xs = before ++ x :: after ∧ P x ∧ ∀ z ∈ before, ¬ P z := by
  induction xs with
  | nil => simp at hit
  | cons a as ih =>
    by_cases ha : P a
    · exact ⟨[], a, as, rfl, ha, by simp⟩
    · have htail : ∃ x ∈ as, P x := by
        obtain ⟨x, hx, hpx⟩ := hit
        rcases List.mem_cons.mp hx with hxa | hxs
        · subst x
          exact (ha hpx).elim
        · exact ⟨x, hxs, hpx⟩
      obtain ⟨before, x, after, heq, hpx, hnone⟩ := ih htail
      refine ⟨a :: before, x, after, by simp [heq], hpx, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with hza | hzb
      · subst z
        exact ha
      · exact hnone z hzb

/-- Before the first opposite trigger, every owner-local query outside the
retained coarse cell lies on the original micro side. -/
theorem original_side_of_not_trigger {q : Gadget} {y p z : Key}
    (hne : y ≠ p) (howner : q.owner.IsPrefix z) (hother : q.coarse z ≠ q.coarse y)
    (hnot : ¬ OppositeTrigger q y p z) :
    (y < p ∧ y < z) ∨ (p < y ∧ z < y) := by
  have hzy : z ≠ y := by
    intro heq
    subst z
    exact hother rfl
  rcases lt_or_gt_of_ne hne with hyp | hpy
  · left
    refine ⟨hyp, ?_⟩
    by_contra hn
    have hzylt : z < y := lt_of_le_of_ne (le_of_not_gt hn) hzy
    exact hnot ⟨howner, hother, Or.inl ⟨hzylt, hyp⟩⟩
  · right
    refine ⟨hpy, ?_⟩
    by_contra hn
    have hyzlt : y < z := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hzy)
    exact hnot ⟨howner, hother, Or.inr ⟨hpy, hyzlt⟩⟩

/-- Construct the actual record at an explicitly chosen first opposite query. -/
def delayedOfFirstOpposite (before earlier : List Key) (q : Gadget) (y p x : Key)
    (hoy : q.owner.IsPrefix y) (hop : q.owner.IsPrefix p)
    (hcoarse : q.coarse y = q.coarse p) (hfine : q.fine y ≠ q.fine p)
    (hretained : ∀ z ∈ earlier, q.owner.IsPrefix z → q.coarse z = q.coarse y →
      q.fine z = q.fine p)
    (hfirst : ∀ z ∈ earlier, ¬ OppositeTrigger q y p z)
    (htrigger : OppositeTrigger q y p x) :
    DelayedEvent (before ++ y :: p :: earlier) x q y where
  before := before
  later := earlier
  next := p
  history_eq := rfl
  owner_source := hoy
  owner_target := htrigger.1
  owner_next := hop
  coarse_same := hcoarse
  coarse_other := Ne.symm htrigger.2.1
  fine_change := hfine
  reversal := htrigger.2.2
  retained := by
    intro z hz howner
    rcases List.mem_cons.mp hz with hzp | hztail
    · subst z
      exact Or.inl rfl
    · by_cases hsame : q.coarse z = q.coarse y
      · exact Or.inl (hretained z hztail howner hsame)
      · refine Or.inr ⟨hsame, ?_⟩
        apply original_side_of_not_trigger _ howner hsame (hfirst z hztail)
        intro hyp
        subst p
        exact hfine rfl

/-- A gap containing any opposite-side query supplies an actual delayed event
at its first such occurrence. The exact prefix is retained for occurrence-level
injections across different gaps. -/
theorem delayed_event_in_gap (before gap : List Key) (q : Gadget) (y p : Key)
    (hoy : q.owner.IsPrefix y) (hop : q.owner.IsPrefix p)
    (hcoarse : q.coarse y = q.coarse p) (hfine : q.fine y ≠ q.fine p)
    (hretained : ∀ z ∈ gap, q.owner.IsPrefix z → q.coarse z = q.coarse y →
      q.fine z = q.fine p)
    (hit : ∃ x ∈ gap, OppositeTrigger q y p x) :
    ∃ earlier x later, gap = earlier ++ x :: later ∧
      OppositeTrigger q y p x ∧
      (∀ z ∈ earlier, ¬ OppositeTrigger q y p z) ∧
      Nonempty (DelayedEvent (before ++ y :: p :: earlier) x q y) := by
  classical
  obtain ⟨earlier, x, later, hgap, htrigger, hfirst⟩ := first_hit_split (OppositeTrigger q y p) gap hit
  refine ⟨earlier, x, later, hgap, htrigger, hfirst, ?_⟩
  refine ⟨delayedOfFirstOpposite before earlier q y p x hoy hop hcoarse hfine ?_ hfirst htrigger⟩
  intro z hz ho hc
  apply hretained z _ ho hc
  rw [hgap]
  exact List.mem_append.mpr (Or.inl hz)

/-- The direction test at the first micro edge gives exactly the reversal
ordering required by an entry event. Coarse-cell convexity is proved through
prefix-order preservation. -/
theorem entry_reversal_of_turn {q : Gadget} {y p x : Key}
    (hcoarse : q.coarse p = q.coarse x) (hother : q.coarse y ≠ q.coarse x)
    (hfine : q.fine p ≠ q.fine x)
    (hturn : decide (y < p) ≠ decide (p < x)) :
    (y < x ∧ x < p) ∨ (p < x ∧ x < y) := by
  have hpxne : p ≠ x := by intro heq; subst x; exact hfine rfl
  have hypne : y ≠ p := by intro heq; subst y; exact hother hcoarse
  have hpother : q.coarse p ≠ q.coarse y := by
    intro heq
    exact hother (heq.symm.trans hcoarse)
  by_cases hyp : y < p
  · have hnpx : ¬ p < x := by intro hpx; simp [hyp, hpx] at hturn
    have hxp : x < p := lt_of_le_of_ne (le_of_not_gt hnpx) (Ne.symm hpxne)
    exact Or.inl ⟨gt_of_take_eq hcoarse.symm hpother hyp, hxp⟩
  · have hpx : p < x := by
      by_contra hnpx
      simp [hyp, hnpx] at hturn
    have hpy : p < y := lt_of_le_of_ne (le_of_not_gt hyp) (Ne.symm hypne)
    exact Or.inr ⟨hpx, lt_of_take_eq hcoarse.symm hpother hpy⟩

/-- Construct the actual entry event from the last outside source, a first-fine
run ending at `p`, and its first nonzero micro transition `p,x`. -/
def entryOfFirstMicroTurn (before middle : List Key) (q : Gadget) (y p x : Key)
    (hoy : q.owner.IsPrefix y) (hop : q.owner.IsPrefix p) (hox : q.owner.IsPrefix x)
    (hcoarse : q.coarse p = q.coarse x) (hother : q.coarse y ≠ q.coarse x)
    (hfine : q.fine p ≠ q.fine x)
    (hturn : decide (y < p) ≠ decide (p < x))
    (hfirst : ∀ z ∈ middle ++ [p], q.owner.IsPrefix z → q.fine z = q.fine p) :
    EntryEvent (before ++ y :: (middle ++ [p])) x q y where
  before := before
  middle := middle
  previous := p
  history_eq := rfl
  owner_source := hoy
  owner_target := hox
  owner_previous := hop
  coarse_same := hcoarse
  coarse_other := hother
  fine_change := hfine
  reversal := entry_reversal_of_turn hcoarse hother hfine hturn
  first_fine := hfirst

end ChaCha.Witnesses
