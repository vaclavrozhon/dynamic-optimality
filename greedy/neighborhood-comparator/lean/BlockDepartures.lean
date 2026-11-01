import BlockLifetime

/-!
Local departure histories for one created shrinking block instance.
Splitting ends that instance and charges any new instances separately.
The block never gains members. A consolidation containing a charged
departure leaves at most one member of the old instance. This derives
the lifetime capacity from a phase capacity and actual set deletions.
-/
namespace GreedyForest.Execution

open scoped BigOperators

structure DepartureStep (Record : Type*) where
  after : Finset Record
  charged : Finset Record

def departureActivity {Record : Type*} : List (DepartureStep Record) → ℕ
  | [] => 0
  | step :: rest => step.charged.card + departureActivity rest

def ValidDepartureRun {Record : Type*} (capacity : ℕ) (before : Finset Record) :
    List (DepartureStep Record) → Prop
  | [] => True
  | step :: rest =>
      step.after ⊆ before ∧ step.charged ⊆ before ∧
      Disjoint step.charged step.after ∧ step.charged.card ≤ capacity ∧
      (0 < step.charged.card → step.after.card ≤ 1) ∧
      ValidDepartureRun capacity step.after rest

/-- The set-transition part, separated from the geometric phase bound. -/
def DepartureTransitions {Record : Type*} (before : Finset Record) :
    List (DepartureStep Record) → Prop
  | [] => True
  | step :: rest =>
      step.after ⊆ before ∧ step.charged ⊆ before ∧
      Disjoint step.charged step.after ∧
      (0 < step.charged.card → step.after.card ≤ 1) ∧
      DepartureTransitions step.after rest

theorem departureTransitions_to_valid {Record : Type*} (capacity : ℕ)
    (before : Finset Record) (steps : List (DepartureStep Record))
    (ht : DepartureTransitions before steps)
    (hc : ∀ step ∈ steps, step.charged.card ≤ capacity) :
    ValidDepartureRun capacity before steps := by
  induction steps generalizing before with
  | nil => trivial
  | cons step rest ih =>
      rcases ht with ⟨ha, hd, hdisj, hcollapse, htail⟩
      exact ⟨ha, hd, hdisj, hc step (by simp), hcollapse,
        ih step.after htail (fun s hs => hc s (by simp [hs]))⟩

theorem departure_step_card {Record : Type*} [DecidableEq Record]
    (before : Finset Record) (step : DepartureStep Record)
    (ha : step.after ⊆ before) (hc : step.charged ⊆ before)
    (hd : Disjoint step.charged step.after) :
    step.charged.card + step.after.card ≤ before.card := by
  have hu := Finset.card_le_card (Finset.union_subset hc ha)
  rwa [Finset.card_union_of_disjoint hd] at hu

/-- Charged records leave and can never be charged again in the same
block instance. This is a set-deletion telescope, independent of labels. -/
theorem departure_activity_le_initial {Record : Type*} [DecidableEq Record]
    (capacity : ℕ) (before : Finset Record) (steps : List (DepartureStep Record))
    (h : ValidDepartureRun capacity before steps) : departureActivity steps ≤ before.card := by
  induction steps generalizing before with
  | nil => simp [departureActivity]
  | cons step rest ih =>
      rcases h with ⟨ha, hc, hd, _, _, htail⟩
      have hstep := departure_step_card before step ha hc hd
      have hrest := ih step.after htail
      simp only [departureActivity]
      omega

/-- The first charged consolidation costs one phase allowance. Its
single surviving old member can be charged at most once in all future
phases combined, even if those phases are separated by administration. -/
theorem departure_activity_le_capacity {Record : Type*} [DecidableEq Record]
    (capacity : ℕ) (before : Finset Record) (steps : List (DepartureStep Record))
    (h : ValidDepartureRun capacity before steps) : departureActivity steps ≤ capacity+1 := by
  induction steps generalizing before with
  | nil => simp [departureActivity]
  | cons step rest ih =>
      rcases h with ⟨_, _, _, hcap, hcollapse, htail⟩
      by_cases hz : step.charged.card = 0
      · simpa [departureActivity, hz] using ih step.after htail
      · have hsmall := hcollapse (Nat.pos_of_ne_zero hz)
        have hrest := departure_activity_le_initial capacity step.after rest htail
        simp only [departureActivity]
        omega

structure DepartureLifetime (stages capacity : ℕ) (count : Fin stages → ℕ) where
  initial : Finset ℕ
  step : Fin stages → DepartureStep ℕ
  census : ∀ p, (step p).charged.card = count p
  valid : ValidDepartureRun capacity initial (List.ofFn step)

theorem departureActivity_ofFn {stages : ℕ} (step : Fin stages → DepartureStep ℕ) :
    departureActivity (List.ofFn step) = ∑ p, (step p).charged.card := by
  have hlist : ∀ steps : List (DepartureStep ℕ),
      departureActivity steps = (steps.map (fun s => s.charged.card)).sum := by
    intro steps
    induction steps with
    | nil => rfl
    | cons s rest ih => simp [departureActivity, ih]
  rw [hlist]
  simp [List.map_ofFn, List.sum_ofFn]

theorem DepartureLifetime.bound {stages capacity : ℕ} {count : Fin stages → ℕ}
    (h : DepartureLifetime stages capacity count) : (∑ p, count p) ≤ capacity+1 := by
  have hb := departure_activity_le_capacity capacity h.initial (List.ofFn h.step) h.valid
  rw [departureActivity_ofFn] at hb
  simpa [h.census] using hb

/-- A history whose charged sets are the actual record images of the
selected phase events. The injection prevents counting one record twice
as two departures from the same block in a phase. -/
structure EventDepartureHistory (Record Event : Type*) [DecidableEq Record]
    (stages : ℕ) (events : Fin stages → Finset Event) (record : Event → Record) where
  initial : Finset Record
  after : Fin stages → Finset Record
  injective : ∀ p, Set.InjOn record (events p)
  transitions : DepartureTransitions initial
    (List.ofFn (fun p => DepartureStep.mk (after p) ((events p).image record)))

theorem EventDepartureHistory.bound {Record Event : Type*} [DecidableEq Record]
    {stages capacity : ℕ} {events : Fin stages → Finset Event} {record : Event → Record}
    (h : EventDepartureHistory Record Event stages events record)
    (hphase : ∀ p, (events p).card ≤ capacity) :
    (∑ p, (events p).card) ≤ capacity+1 := by
  let step := fun p => DepartureStep.mk (h.after p) ((events p).image record)
  have hcensus : ∀ p, (step p).charged.card = (events p).card := by
    intro p
    exact Finset.card_image_of_injOn (h.injective p)
  have hc : ∀ s ∈ List.ofFn step, s.charged.card ≤ capacity := by
    intro s hs
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hs
    subst s
    rw [hcensus]
    exact hphase p
  have hv := departureTransitions_to_valid capacity h.initial (List.ofFn step) h.transitions hc
  have hb := departure_activity_le_capacity capacity h.initial (List.ofFn step) hv
  have htelescope : departureActivity (List.ofFn step) = ∑ p, (step p).charged.card := by
    have hlist : ∀ steps : List (DepartureStep Record),
        departureActivity steps = (steps.map (fun s => s.charged.card)).sum := by
      intro steps
      induction steps with
      | nil => rfl
      | cons s rest ih => simp [departureActivity, ih]
    rw [hlist]
    simp [List.map_ofFn, List.sum_ofFn]
  rw [htelescope] at hb
  simpa [hcensus] using hb

structure EventDepartureLifetime (Record Event : Type*) [DecidableEq Record]
    (stages capacity : ℕ) (events : Fin stages → Finset Event) (record : Event → Record)
    extends EventDepartureHistory Record Event stages events record where
  phaseBound : ∀ p, (events p).card ≤ capacity

theorem EventDepartureLifetime.bound {Record Event : Type*} [DecidableEq Record]
    {stages capacity : ℕ} {events : Fin stages → Finset Event} {record : Event → Record}
    (h : EventDepartureLifetime Record Event stages capacity events record) :
    (∑ p, (events p).card) ≤ capacity+1 :=
  h.toEventDepartureHistory.bound h.phaseBound

/-- Turn locally proved fiber capacities into explicit slots. No slot
injection is assumed: its existence follows from finite cardinalities. -/
theorem exists_sum_slots {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [DecidableEq C]
    (tag : A → Sum B C) (capacity : ℕ)
    (hcapacity : ∀ b, Fintype.card {a // tag a = Sum.inl b} ≤ capacity)
    (hright : ∀ a a' c, tag a = Sum.inr c → tag a' = Sum.inr c → a = a') :
    ∃ charge : A → Sum (B × Fin capacity) C, Function.Injective charge ∧
      ∀ a, Sum.map Prod.fst id (charge a) = tag a := by
  classical
  have he : ∀ b, Nonempty ({a // tag a = Sum.inl b} ↪ Fin capacity) := by
    intro b
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcapacity b
  let embed := fun b => Classical.choice (he b)
  let charge : A → Sum (B × Fin capacity) C := fun a =>
    match ht : tag a with
    | Sum.inl b => Sum.inl (b, embed b ⟨a, ht⟩)
    | Sum.inr c => Sum.inr c
  refine ⟨charge, ?_, ?_⟩
  · intro a a' hh
    dsimp only [charge] at hh
    split at hh <;> split at hh
    · rename_i b hb b' hb'
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hh
      rcases hh with ⟨rfl, hslots⟩
      exact congrArg Subtype.val ((embed b).injective hslots)
    · contradiction
    · contradiction
    · rename_i c hc c' hc'
      have heq : c = c' := Sum.inr.inj hh
      subst c'
      exact hright a a' c hc hc'
  · intro a
    dsimp only [charge]
    split <;> simp_all

end GreedyForest.Execution
