import ChaCha.Witnesses
import ChaCha.CyclicPrimaryBudget

/-!
# Actual event budgets in the second period

An initial copy of the closed word supplies genuine preceding accesses for
cyclic witnesses. Events are then counted on the second copy alone.
-/

namespace ChaCha
open Primary Witnesses MTR MTR.Tree NormalizedWords

/-- Include the terminal auxiliary fragments used only for telescoping. -/
def allGadgets (H : Nat) : Finset Gadget :=
  (((DepthTree.midpoint 0 H (Nat.zero_le H)).nodes ×ˢ owners H).filter
    (fun q => q.2.length = q.1.lo)).image (fun q => ⟨q.1, q.2⟩)

theorem mem_allGadgets {H : Nat} {q : Gadget} : q ∈ allGadgets H ↔
    q.split ∈ (DepthTree.midpoint 0 H (Nat.zero_le H)).nodes ∧
    q.owner ∈ owners H ∧ q.owner.length = q.split.lo := by
  cases q
  simp [allGadgets, and_assoc]

theorem allGadgets_valid {H : Nat} {q : Gadget} (hq : q ∈ allGadgets H) : Valid H q := by
  obtain ⟨hs, _, hl⟩ := mem_allGadgets.mp hq
  exact ⟨hs, hl⟩

theorem gadgets_subset_all (H : Nat) : gadgets H ⊆ allGadgets H := by
  intro q hq
  obtain ⟨hs, hu, hl, _⟩ := mem_gadgets.mp hq
  exact mem_allGadgets.mpr ⟨hs, hu, hl⟩

noncomputable def eventSum (H : Nat) (qs : Finset Gadget) : List Key → List Key → Nat
  | _, [] => 0
  | history, x :: xs => (activeEvents H qs history x).card + eventSum H qs (history ++ [x]) xs

noncomputable def periodEvents (H : Nat) (xs : List Key) : Nat :=
  eventSum H (allGadgets H) xs xs

/-- A two-period charging window after one prior period. This allows forward
gap assignments across the period boundary without reducing times modulo it. -/
noncomputable def twoPeriodEvents (H : Nat) (xs : List Key) : Nat :=
  eventSum H (allGadgets H) xs (xs ++ xs)

/-- Sum concrete record budgets along an actual execution suffix. -/
theorem eventSum_budget {H : Nat} (qs : Finset Gadget) (valid : ∀ q ∈ qs, Valid H q)
    (t : Tree Key) (history xs : List Key)
    (hn : Normalized (initialPreference H t) H (history ++ xs))
    (hs : Successful t (history ++ xs)) (hl : OnLeaves H (history ++ xs)) :
    eventSum H qs history xs ≤ internalSearchVisits (run t history) xs := by
  induction xs generalizing history with
  | nil => simp [eventSum, internalSearchVisits]
  | cons x xs ih =>
    have hs' := (successful_append t history (x :: xs)).mp hs
    obtain ⟨d, hd⟩ := hs'.2.1
    have hone : OneFlip (initialPreference H t) H history x := hn history x xs rfl
    have hl' : OnLeaves H (history ++ [x]) := by
      intro y hy
      apply hl y
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · simp [hy]
      · simp
    have hb := activeEvents_budget qs valid hl' (initialPreference H t) hone t hs'.1 d hd
    have hi := ih (history ++ [x])
      (by simpa only [List.append_assoc, List.singleton_append] using hn)
      (by simpa only [List.append_assoc, List.singleton_append] using hs)
      (by simpa only [List.append_assoc, List.singleton_append] using hl)
    have hr : run t (history ++ [x]) = moveToRoot x (run t history) := by
      rw [run_append]
      rfl
    rw [hr] at hi
    simp only [eventSum, internalSearchVisits, hd, Option.getD_some]
    omega

/-- Repeating a closed normalized actual execution yields real cyclic history. -/
theorem normalized_two_periods {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs)
    (hl : ∀ x ∈ xs, x.length = H) (hc : run t xs = t) :
    Normalized (initialPreference H t) H (xs ++ xs) ∧ Successful t (xs ++ xs) ∧
      OnLeaves H (xs ++ xs) := by
  have ha : AmbientNormalized H t (xs ++ xs) :=
    (ambientNormalized_append H t xs xs).mpr ⟨hn, hc.symm ▸ hn⟩
  have hs' : Successful t (xs ++ xs) :=
    (successful_append t xs xs).mpr ⟨hs, hc.symm ▸ hs⟩
  have hl' : OnLeaves H (xs ++ xs) := by
    intro x hx
    exact hl x (by simpa using hx)
  exact ⟨ambientNormalized_history ha hs' hl', hs', hl'⟩

theorem periodEvents_budget {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs)
    (hl : ∀ x ∈ xs, x.length = H) (hc : run t xs = t) :
    periodEvents H xs ≤ internalSearchVisits t xs := by
  obtain ⟨hn', hs', hl'⟩ := normalized_two_periods hn hs hl hc
  have h := eventSum_budget (allGadgets H) (fun _ hq => allGadgets_valid hq) t xs xs hn' hs' hl'
  simpa only [periodEvents, hc] using h

theorem internalSearchVisits_append (t : Tree Key) (xs ys : List Key) :
    internalSearchVisits t (xs ++ ys) =
      internalSearchVisits t xs + internalSearchVisits (run t xs) ys := by
  induction xs generalizing t with
  | nil => simp [internalSearchVisits, run]
  | cons x xs ih => simp [internalSearchVisits, run, ih, Nat.add_assoc]

/-- A fixed number of complete copies, with their actual order retained. -/
def repeatWord (xs : List Key) : Nat → List Key
  | 0 => []
  | n + 1 => xs ++ repeatWord xs n

theorem run_repeatWord {t : Tree Key} {xs : List Key} (hc : run t xs = t) (n : Nat) :
    run t (repeatWord xs n) = t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatWord, run_append, hc, ih]

theorem normalized_repeatWord {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hc : run t xs = t) (n : Nat) :
    AmbientNormalized H t (repeatWord xs n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact (ambientNormalized_append _ _ _ _).mpr ⟨hn, hc.symm ▸ ih⟩

theorem successful_repeatWord {t : Tree Key} {xs : List Key}
    (hs : Successful t xs) (hc : run t xs = t) (n : Nat) :
    Successful t (repeatWord xs n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact (MTR.successful_append _ _ _).mpr ⟨hs, hc.symm ▸ ih⟩

theorem leaves_repeatWord {H : Nat} {xs : List Key} (hl : OnLeaves H xs) (n : Nat) :
    OnLeaves H (repeatWord xs n) := by
  induction n with
  | zero => intro x hx; simp [repeatWord] at hx
  | succ n ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hl x hx
    · exact ih x hx

/-- The analytical last-access preferences are normalized on every finite
number of repetitions of an actual closed normalized execution. -/
theorem history_normalized_repeatWord {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t) (n : Nat) :
    Normalized (initialPreference H t) H (repeatWord xs n) :=
  ambientNormalized_history (normalized_repeatWord hn hc n)
    (successful_repeatWord hs hc n) (leaves_repeatWord hl n)

theorem internalSearchVisits_repeatWord {t : Tree Key} {xs : List Key}
    (hc : run t xs = t) (n : Nat) :
    internalSearchVisits t (repeatWord xs n) = n * internalSearchVisits t xs := by
  induction n with
  | zero => simp [repeatWord, internalSearchVisits]
  | succ n ih => rw [repeatWord, internalSearchVisits_append, hc, ih, Nat.succ_mul]; omega

/-- Any finite period window has a budget proportional to its number of copies,
regardless of how many earlier real copies supply the source history. -/
theorem repeated_event_window_budget {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t) (prior window : Nat) :
    eventSum H (allGadgets H) (repeatWord xs prior) (repeatWord xs window) ≤
      window * internalSearchVisits t xs := by
  have hp := run_repeatWord hc prior
  have ha : AmbientNormalized H t (repeatWord xs prior ++ repeatWord xs window) :=
    (ambientNormalized_append _ _ _ _).mpr
      ⟨normalized_repeatWord hn hc prior, hp.symm ▸ normalized_repeatWord hn hc window⟩
  have hs' : Successful t (repeatWord xs prior ++ repeatWord xs window) :=
    (MTR.successful_append _ _ _).mpr
      ⟨successful_repeatWord hs hc prior, hp.symm ▸ successful_repeatWord hs hc window⟩
  have hl' : OnLeaves H (repeatWord xs prior ++ repeatWord xs window) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact leaves_repeatWord hl prior x hx
    · exact leaves_repeatWord hl window x hx
  have hb := eventSum_budget (allGadgets H) (fun _ hq => allGadgets_valid hq) t _ _
    (ambientNormalized_history ha hs' hl') hs' hl'
  simpa only [hp, internalSearchVisits_repeatWord hc] using hb

noncomputable def threePeriodEvents (H : Nat) (xs : List Key) : Nat :=
  eventSum H (allGadgets H) xs (xs ++ (xs ++ xs))

theorem threePeriodEvents_budget {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t) :
    threePeriodEvents H xs ≤ 3 * internalSearchVisits t xs := by
  simpa only [threePeriodEvents, repeatWord, List.append_nil] using
    repeated_event_window_budget hn hs hl hc 1 3

/-- A complete four-copy history, indexed from zero, avoids translating local
occurrence times into a shifted payment window. -/
noncomputable def fourPeriodEvents (H : Nat) (xs : List Key) : Nat :=
  eventSum H (allGadgets H) [] (xs ++ (xs ++ (xs ++ xs)))

theorem fourPeriodEvents_budget {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs) (hl : OnLeaves H xs)
    (hc : run t xs = t) :
    fourPeriodEvents H xs ≤ 4 * internalSearchVisits t xs := by
  simpa only [fourPeriodEvents, repeatWord, List.append_nil] using
    repeated_event_window_budget hn hs hl hc 0 4

theorem twoPeriodEvents_budget {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs)
    (hl : ∀ x ∈ xs, x.length = H) (hc : run t xs = t) :
    twoPeriodEvents H xs ≤ 2 * internalSearchVisits t xs := by
  have ha₂ : AmbientNormalized H t (xs ++ xs) :=
    (ambientNormalized_append H t xs xs).mpr ⟨hn, hc.symm ▸ hn⟩
  have hs₂ : Successful t (xs ++ xs) :=
    (successful_append t xs xs).mpr ⟨hs, hc.symm ▸ hs⟩
  have ha₃ : AmbientNormalized H t (xs ++ (xs ++ xs)) :=
    (ambientNormalized_append H t xs (xs ++ xs)).mpr ⟨hn, hc.symm ▸ ha₂⟩
  have hs₃ : Successful t (xs ++ (xs ++ xs)) :=
    (successful_append t xs (xs ++ xs)).mpr ⟨hs, hc.symm ▸ hs₂⟩
  have hl₃ : OnLeaves H (xs ++ (xs ++ xs)) := by
    intro x hx
    exact hl x (by simpa using hx)
  have hn₃ := ambientNormalized_history ha₃ hs₃ hl₃
  have hb := eventSum_budget (allGadgets H) (fun _ hq => allGadgets_valid hq)
    t xs (xs ++ xs) hn₃ hs₃ hl₃
  simpa only [twoPeriodEvents, hc, internalSearchVisits_append, Nat.two_mul] using hb

/-- The cyclic primary count and all concrete per-period record events fit
together into the actual Move-to-Root rotation budget. -/
theorem primary_and_period_events_budget {H : Nat} {t : Tree Key} {xs : List Key}
    (hn : AmbientNormalized H t xs) (hs : Successful t xs)
    (hl : ∀ x ∈ xs, x.length = H) (hc : run t xs = t) :
    cyclicPrimary H xs + periodEvents H xs ≤ rotationCount t xs := by
  have he := periodEvents_budget hn hs hl hc
  have hp := cyclicPrimary_add_internalSearchVisits_le_rotations hn hs hl hc
  omega

end ChaCha
