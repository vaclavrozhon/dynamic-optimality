import Mathlib

/-!
Growth windows read from actual membership-ticket batches in one
persistent creator slot. Appending a fresh entry extends only the current
batch; replacing the grower closes that batch and installs a fresh family
name. Births need not occupy distinct elementary label times. Min/max
actual entry times define the windows, and singleton or empty families
have zero-length windows automatically.
-/
namespace GreedyMerge.GrowthWindows

structure Batch where
  family : ℕ
  joined : List ℕ
  deriving DecidableEq

def allTimes (journal : List Batch) : List ℕ := journal.flatMap Batch.joined

def collect (family : ℕ) (journal : List Batch) : List ℕ :=
  journal.flatMap (fun batch => if batch.family=family then batch.joined else [])

def Valid (journal : List Batch) : Prop :=
  (journal.map Batch.family).Nodup ∧ (allTimes journal).Pairwise (· < ·)

noncomputable def start (joined : List ℕ) : ℕ :=
  if present : joined.toFinset.Nonempty then joined.toFinset.min' present else 0

noncomputable def finish (joined : List ℕ) : ℕ :=
  if present : joined.toFinset.Nonempty then joined.toFinset.max' present else 0

noncomputable def growthStart (family : ℕ) (journal : List Batch) : ℕ := start (collect family journal)
noncomputable def growthEnd (family : ℕ) (journal : List Batch) : ℕ := finish (collect family journal)

theorem member_between (joined : List ℕ) (time : ℕ) (member : time∈joined) :
    start joined≤time ∧ time≤finish joined := by
  have inSet := List.mem_toFinset.mpr member
  have present : joined.toFinset.Nonempty := ⟨time,inSet⟩
  simp only [start,finish,dif_pos present]
  exact ⟨Finset.min'_le _ _ inSet,Finset.le_max' _ _ inSet⟩

theorem active_extrema (joined : List ℕ) (time : ℕ)
    (_started : start joined≤time) (active : time<finish joined) :
    start joined∈joined ∧ finish joined∈joined := by
  by_cases present : joined.toFinset.Nonempty
  · simp only [start,finish,dif_pos present]
    exact ⟨List.mem_toFinset.mp (Finset.min'_mem _ present),List.mem_toFinset.mp (Finset.max'_mem _ present)⟩
  · simp only [finish,dif_neg present] at active
    omega

theorem finish_le_horizon (joined : List ℕ) (horizon : ℕ)
    (bounded : ∀ time∈joined, time≤horizon) : finish joined≤horizon := by
  by_cases present : joined.toFinset.Nonempty
  · simp only [finish,dif_pos present]
    exact Finset.max'_le _ _ _ (fun time member => bounded time (List.mem_toFinset.mp member))
  · simp only [finish,dif_neg present]
    omega

@[simp] theorem singleton_start (time : ℕ) : start [time]=time := by simp [start]
@[simp] theorem singleton_finish (time : ℕ) : finish [time]=time := by simp [finish]
@[simp] theorem empty_start : start []=0 := by simp [start]
@[simp] theorem empty_finish : finish []=0 := by simp [finish]

theorem collect_member (family time : ℕ) (journal : List Batch) :
    time∈collect family journal ↔ ∃ batch∈journal, batch.family=family ∧ time∈batch.joined := by
  constructor
  · intro member
    obtain ⟨batch,present,member⟩ := List.mem_flatMap.mp member
    by_cases same : batch.family=family
    · exact ⟨batch,present,same,by simpa only [if_pos same] using member⟩
    · simp only [if_neg same,List.not_mem_nil] at member
  · rintro ⟨batch,present,same,member⟩
    exact List.mem_flatMap.mpr ⟨batch,present,by simpa only [if_pos same] using member⟩

theorem collect_absent (family : ℕ) (journal : List Batch)
    (absent : family∉journal.map Batch.family) : collect family journal=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro time member
  obtain ⟨batch,present,same,_⟩ := (collect_member family time journal).mp member
  exact absent (List.mem_map.mpr ⟨batch,present,same⟩)

/-- A family tag never returns after replacement, so all of its actual
entries are exactly one literal batch of the per-slot journal. -/
theorem collect_eq_batch (journal : List Batch) (unique : (journal.map Batch.family).Nodup)
    (batch : Batch) (present : batch∈journal) : collect batch.family journal=batch.joined := by
  induction journal with
  | nil => simp at present
  | cons first rest ih =>
      have h := List.nodup_cons.mp unique
      rcases List.mem_cons.mp present with rfl | later
      · have empty := collect_absent batch.family rest h.1
        simp only [collect,List.flatMap_cons]
        change batch.joined++collect batch.family rest=batch.joined
        rw [empty,List.append_nil]
      · have different : first.family≠batch.family := by
          intro same
          exact h.1 (List.mem_map.mpr ⟨batch,later,same.symm⟩)
        simp only [collect,List.flatMap_cons,if_neg different,List.nil_append]
        exact ih h.2 later

/-- Two distinct tags cannot have overlapping min/max entry windows in
one literal chronological slot journal. No overlap capacity is assumed. -/
theorem one_active_family (journal : List Batch) (valid : Valid journal)
    (first second time : ℕ)
    (firstStart : growthStart first journal≤time) (firstEnd : time<growthEnd first journal)
    (secondStart : growthStart second journal≤time) (secondEnd : time<growthEnd second journal) :
    first=second := by
  have firstExt := active_extrema (collect first journal) time firstStart firstEnd
  have secondExt := active_extrema (collect second journal) time secondStart secondEnd
  obtain ⟨a,aMember,aFamily,_⟩ := (collect_member first _ journal).mp firstExt.1
  obtain ⟨b,bMember,bFamily,_⟩ := (collect_member second _ journal).mp secondExt.1
  have aTimes : collect first journal=a.joined := by rw [←aFamily]; exact collect_eq_batch journal valid.1 a aMember
  have bTimes : collect second journal=b.joined := by rw [←bFamily]; exact collect_eq_batch journal valid.1 b bMember
  change start (collect first journal)≤time at firstStart
  change time<finish (collect first journal) at firstEnd
  change start (collect second journal)≤time at secondStart
  change time<finish (collect second journal) at secondEnd
  rw [aTimes] at firstStart firstEnd firstExt
  rw [bTimes] at secondStart secondEnd secondExt
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp aMember
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp bMember
  have cross := (List.pairwise_flatMap.mp valid.2).2
  rcases lt_trichotomy i j with before | same | after
  · have order := cross.rel_get_of_lt before
    rw [hi,hj] at order
    have impossible := order _ firstExt.2 _ secondExt.1
    omega
  · subst j
    exact aFamily.symm.trans (hi.symm.trans hj |> congrArg Batch.family) |>.trans bFamily
  · have order := cross.rel_get_of_lt after
    rw [hi,hj] at order
    have impossible := order _ secondExt.2 _ firstExt.1
    omega

/-- Literal current-slot implementation: closed batches followed by one
current grower. Family names are replaced, never reopened. -/
structure SlotState where
  closed : List Batch
  current : Batch

def journal (state : SlotState) : List Batch := state.closed++[state.current]

def appendEntry (time : ℕ) (state : SlotState) : SlotState :=
  { state with current := { state.current with joined := state.current.joined++[time] } }

def replace (family : ℕ) (state : SlotState) : SlotState :=
  ⟨state.closed++[state.current],⟨family,[]⟩⟩

@[simp] theorem appendEntry_families (time : ℕ) (state : SlotState) :
    (journal (appendEntry time state)).map Batch.family=(journal state).map Batch.family := by
  simp [journal,appendEntry]

@[simp] theorem appendEntry_times (time : ℕ) (state : SlotState) :
    allTimes (journal (appendEntry time state))=allTimes (journal state)++[time] := by
  simp [allTimes,journal,appendEntry,List.append_assoc]

@[simp] theorem replace_families (family : ℕ) (state : SlotState) :
    (journal (replace family state)).map Batch.family=(journal state).map Batch.family++[family] := by
  simp [journal,replace]

@[simp] theorem replace_times (family : ℕ) (state : SlotState) :
    allTimes (journal (replace family state))=allTimes (journal state) := by
  simp [allTimes,journal,replace]

inductive SlotEdit : SlotState → SlotState → Prop
  | append (state : SlotState) (time : ℕ)
      (fresh : ∀ old∈allTimes (journal state), old<time) : SlotEdit state (appendEntry time state)
  | replace (state : SlotState) (family : ℕ)
      (fresh : family∉(journal state).map Batch.family) : SlotEdit state (replace family state)

theorem SlotEdit.valid {before after : SlotState} (edit : SlotEdit before after)
    (valid : Valid (journal before)) : Valid (journal after) := by
  cases edit with
  | append time fresh =>
      constructor
      · simpa using valid.1
      · rw [appendEntry_times]
        apply List.pairwise_append.mpr
        exact ⟨valid.2,by simp,fun old member last lastMember => by
          have same := List.mem_singleton.mp lastMember
          simpa only [same] using fresh old member⟩
  | replace family fresh =>
      constructor
      · rw [replace_families]
        simpa using (List.nodup_append.mpr ⟨valid.1,List.nodup_singleton _,by simpa using fresh⟩)
      · simpa using valid.2

inductive SlotRun : SlotState → SlotState → Prop
  | nil (state : SlotState) : SlotRun state state
  | cons {before middle after : SlotState} (edit : SlotEdit before middle)
      (rest : SlotRun middle after) : SlotRun before after

theorem SlotRun.valid {before after : SlotState} (run : SlotRun before after)
    (valid : Valid (journal before)) : Valid (journal after) := by
  induction run with
  | nil state => exact valid
  | cons edit rest ih => exact ih (edit.valid valid)


theorem start_le_finish (joined : List ℕ) : start joined≤finish joined := by
  by_cases present : joined.toFinset.Nonempty
  · obtain ⟨time,member⟩ := present
    exact (member_between joined time (List.mem_toFinset.mp member)).1.trans
      (member_between joined time (List.mem_toFinset.mp member)).2
  · simp only [start,finish,dif_neg present,le_refl]

theorem entryInGrowth (family time : ℕ) (journal : List Batch) (batch : Batch)
    (present : batch∈journal) (same : batch.family=family) (member : time∈batch.joined) :
    growthStart family journal≤time ∧ time≤growthEnd family journal :=
  member_between _ _ ((collect_member family time journal).mpr ⟨batch,present,same,member⟩)

theorem growthFinish (family horizon : ℕ) (journal : List Batch)
    (bounded : ∀ time∈allTimes journal, time≤horizon) : growthEnd family journal≤horizon := by
  apply finish_le_horizon
  intro time member
  obtain ⟨batch,present,_,entry⟩ := (collect_member family time journal).mp member
  exact bounded time (List.mem_flatMap.mpr ⟨batch,present,entry⟩)

/-- A whole creator-slot book supplies the exact oneGrowthSlot interface.
Fresh family-name injectivity converts equality of literal journal tags
back to equality of actual family occurrences. -/
theorem oneGrowthSlot {Record Slot Family : Type*}
    (journals : Record → Slot → List Batch) (valid : ∀ creator slot, Valid (journals creator slot))
    (name : Family → ℕ) (namesUnique : Function.Injective name)
    (creator : Family → Record) (slot : Family → Slot)
    (first second : Family) (time : ℕ)
    (sameCreator : creator first=creator second) (sameSlot : slot first=slot second)
    (firstStart : growthStart (name first) (journals (creator first) (slot first))≤time)
    (firstEnd : time<growthEnd (name first) (journals (creator first) (slot first)))
    (secondStart : growthStart (name second) (journals (creator second) (slot second))≤time)
    (secondEnd : time<growthEnd (name second) (journals (creator second) (slot second))) :
    first=second := by
  apply namesUnique
  rw [sameCreator,sameSlot] at firstStart firstEnd
  exact one_active_family _ (valid _ _) _ _ time firstStart firstEnd secondStart secondEnd

/-- Empty and temporary singleton families consume no positive-length
growth window, irrespective of how many are born at the same boundary. -/
theorem no_singleton_growth (time point : ℕ) : ¬(start [time]≤point ∧ point<finish [time]) := by
  simp only [singleton_start,singleton_finish]
  omega

end GreedyMerge.GrowthWindows

#print axioms GreedyMerge.GrowthWindows.one_active_family
#print axioms GreedyMerge.GrowthWindows.SlotRun.valid

#print axioms GreedyMerge.GrowthWindows.oneGrowthSlot
#print axioms GreedyMerge.GrowthWindows.entryInGrowth
