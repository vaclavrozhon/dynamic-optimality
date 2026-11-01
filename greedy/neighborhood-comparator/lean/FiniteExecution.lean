import ExecutionTrace
import CutGeometry
import BlockDepartures
import DepartureGeometry
import HarmfulDepartureGeometry
import WinnerGeometry

/-!
The finite execution interface. The charged exceptions are concrete slots
and local update cells. Historical multiplicities are supplied as local
block-phase traces, not as aggregate shift bounds.
-/
namespace GreedyForest.Execution

-- All local projections share the same finite trace interface; some
-- projection lemmas use only a subset of its finite-type instances.
set_option linter.unusedSectionVars false

open scoped BigOperators

theorem runActivity_eq_sum_counts (steps : List (Family ℕ × ℕ)) :
    runActivity steps = (steps.map Prod.snd).sum := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp [runActivity, ih]

theorem runActivity_ofFn {stages : ℕ} (state : Fin stages → Family ℕ) (count : Fin stages → ℕ) :
    runActivity (List.ofFn (fun p => (state p, count p))) = ∑ p, count p := by
  rw [runActivity_eq_sum_counts]
  simp [List.map_ofFn, List.sum_ofFn]

theorem sum_stage_counts {A : Type*} [Fintype A] {stages : ℕ}
    (stage : A → Fin stages) (selected : A → Prop) [DecidablePred selected] :
    (∑ p, (Finset.univ.filter (fun e => selected e ∧ stage e = p)).card) =
      (Finset.univ.filter selected).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter selected) Finset.univ stage
  simpa [Finset.filter_filter] using h

structure WinnerLifetime (stages join : ℕ) (wins : Fin stages → ℕ) where
  initial : Family ℕ
  after : Fin stages → Family ℕ
  transitions : FamilyTransitions join initial (List.ofFn (fun p => (after p, wins p)))
  geometry : ∀ p, WinnerPhaseGeometry (wins p)

theorem WinnerLifetime.bound {stages join : ℕ} {wins : Fin stages → ℕ}
    (h : WinnerLifetime stages join wins) : (∑ p, wins p) ≤ 4 := by
  have hg : ∀ step ∈ List.ofFn (fun p => (h.after p, wins p)),
      Nonempty (WinnerPhaseGeometry step.2) := by
    intro step hs
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hs
    subst step
    exact ⟨h.geometry p⟩
  have hv := familyTransitions_to_valid h.initial _ h.transitions hg
  rw [← runActivity_ofFn h.after wins]
  exact family_activity_le_degree join 4 h.initial _ hv

structure CutLifetime (stages cut k : ℕ) (crossings : Fin stages → ℕ) where
  initial : Family ℕ
  after : Fin stages → Family ℕ
  transitions : CutTransitions cut initial
    (List.ofFn (fun p => (after p, crossings p)))
  geometry : ∀ p, CutPhaseGeometry k (crossings p)

theorem CutLifetime.bound {stages cut k : ℕ} {crossings : Fin stages → ℕ}
    (h : CutLifetime stages cut k crossings) (hk : 1 ≤ k) : (∑ p, crossings p) ≤ k+1 := by
  have hg : ∀ step ∈ List.ofFn (fun p => (h.after p, crossings p)),
      Nonempty (CutPhaseGeometry k step.2) := by
    intro step hs
    obtain ⟨p, hp⟩ := List.mem_ofFn.mp hs
    subst step
    exact ⟨h.geometry p⟩
  have hv := cutTransitions_to_valid h.initial _ hk h.transitions hg
  rw [← runActivity_ofFn h.after crossings]
  exact cut_activity_le_capacity _ _ h.initial _ hv

variable (Record Good Boundary Bad Member RootBlock Block Paid Ordinary : Type*)
  [Fintype Record] [Fintype Good] [Fintype Boundary] [Fintype Bad]
  [Fintype Member] [Fintype RootBlock] [Fintype Block] [Fintype Paid] [Fintype Ordinary]
  [DecidableEq Record] [DecidableEq Good] [DecidableEq Boundary] [DecidableEq Bad]
  [DecidableEq Member] [DecidableEq RootBlock] [DecidableEq Block]
  [DecidableEq Paid]

structure AccountingTrace (k : ℕ) where
  time : ℕ
  -- All local projections use the same finite stage order.
  stages : ℕ
  label : Record → ℕ → ℤ
  labelBounds : ∀ v t, t ≤ time → 1 ≤ label v t ∧ label v t ≤ (k:ℤ)
  -- Harmful departures carry their source block and actual phase.
  -- Four lifetime slots are derived from these local deletion histories.
  positiveOrigin : {cell : Record × Fin time // 0 < labelDelta time label cell} →
    Sum Block Paid
  positiveStage : {cell : Record × Fin time // 0 < labelDelta time label cell} → Fin stages
  positivePaidUnique : ∀ a a' p,
    positiveOrigin a = Sum.inr p → positiveOrigin a' = Sum.inr p → a = a'
  positiveHistory : ∀ b, HarmfulEventLifetime Record
    {cell : Record × Fin time // 0 < labelDelta time label cell} stages
    (fun p => Finset.univ.filter (fun e =>
      positiveOrigin e = Sum.inl b ∧ positiveStage e = p)) (fun e => e.val.1)
  goodCell : Good → Record × Fin time
  goodInjective : Function.Injective goodCell
  goodDrop : ∀ e, labelDelta time label (goodCell e) ≤ -1
  boundaryOrigin : Boundary → Sum Block (Record × Fin time)
  boundaryRecord : Boundary → Record
  boundaryStage : Boundary → Fin stages
  boundaryDropUnique : ∀ a a' cell,
    boundaryOrigin a = Sum.inr cell → boundaryOrigin a' = Sum.inr cell → a = a'
  boundaryDrop : ∀ e cell, boundaryOrigin e = Sum.inr cell → labelDelta time label cell ≤ -1
  boundaryHistory : ∀ b, BoundaryEventLifetime Record Boundary stages k
    (fun p => Finset.univ.filter (fun e =>
      boundaryOrigin e = Sum.inl b ∧ boundaryStage e = p)) boundaryRecord
  -- Fixed creator and chronological membership snapshots.
  memberRecord : Member → Record
  memberFamily : Member → RootBlock
  memberJoin : Member → ℕ
  memberEnd : Member → ℕ
  memberTimes : ∀ m, memberJoin m ≤ memberEnd m ∧ memberEnd m ≤ time
  familyCreator : RootBlock → Record
  growthStart : RootBlock → ℕ
  growthEnd : RootBlock → ℕ
  growthFinish : ∀ b, growthEnd b ≤ time
  entryInGrowth : ∀ m,
    growthStart (memberFamily m) ≤ memberJoin m ∧ memberJoin m ≤ growthEnd (memberFamily m)
  origin : Member → Option Bad
  entryOrder : List Member
  orderNodup : entryOrder.Nodup
  orderComplete : ∀ m, m ∈ entryOrder
  orderChronological : entryOrder.Pairwise (fun a b => memberJoin a < memberJoin b)
  exceptionalOrigin : {m // (origin m).isNone} →
    Sum Record (Sum Ordinary (Sum Good Boundary))
  exceptionalInjective : Function.Injective exceptionalOrigin
  winnerEntry : Bad → Member
  loserEntry : Bad → Member
  linkTime : Bad → ℕ
  sameFamily : ∀ e, memberFamily (winnerEntry e) = memberFamily (loserEntry e)
  winnerTimes : ∀ e,
    memberJoin (winnerEntry e) ≤ linkTime e ∧ linkTime e ≤ memberEnd (winnerEntry e)
  -- One finite stage order is shared by every family projection. Stages
  -- include both complete consolidations and intervening administration.
  badStage : Bad → Fin stages
  badEntryStrict : ∀ m, (origin m).isSome →
    label (familyCreator (memberFamily m)) (memberJoin m) + 1 ≤
      label (memberRecord m) (memberJoin m)
  badEntryFrame : ∀ m e, origin m = some e →
    familyCreator (memberFamily m) = memberRecord (winnerEntry e) ∧
    memberRecord m = memberRecord (loserEntry e) ∧ memberJoin m = linkTime e
  -- At most one membership interval of a record can be active.
  oneMembership : ∀ v t a b,
    memberRecord a = v → memberJoin a ≤ t → t < memberEnd a →
    memberRecord b = v → memberJoin b ≤ t → t < memberEnd b → a = b
  -- Two persistent growers and one temporary singleton slot per creator.
  growthSlot : RootBlock → Fin 3
  oneGrowthSlot : ∀ v t a b,
    familyCreator a = v → growthStart a ≤ t → t < growthEnd a →
    familyCreator b = v → growthStart b ≤ t → t < growthEnd b →
    growthSlot a = growthSlot b → a = b
  winnerHistory : ∀ m, WinnerLifetime stages (memberJoin m)
    (fun p => (Finset.univ.filter (fun e => winnerEntry e = m ∧ badStage e = p)).card)
  -- A label change at t separates entries joined by t from later
  -- entries. On integer join times the geometric cut is therefore t+1.
  cutHistory : ∀ b t, CutLifetime stages (t+1) k
    (fun p => (Finset.univ.filter (fun e => (memberFamily (winnerEntry e) = b ∧
      min (memberJoin (winnerEntry e)) (memberJoin (loserEntry e)) ≤ t ∧
      t < max (memberJoin (winnerEntry e)) (memberJoin (loserEntry e))) ∧ badStage e = p)).card)
  -- Every bad edge creates exactly one entry in the chronological list.
  badNodup : (entryBadEdges (entryOrder.map (fun m =>
    EntryEvent.mk (memberRecord m)
      (label (familyCreator (memberFamily m)) (memberJoin m)) (origin m)))).Nodup
  badComplete : ∀ e, e ∈ entryBadEdges (entryOrder.map (fun m =>
    EntryEvent.mk (memberRecord m)
      (label (familyCreator (memberFamily m)) (memberJoin m)) (origin m)))
  -- Local previous-creator memory equality at each chronological entry.
  entryLedger : ValidEntryLedger (k:ℤ)
    (fun e => label (memberRecord (winnerEntry e)) (linkTime e) -
      label (familyCreator (memberFamily (loserEntry e))) (memberJoin (loserEntry e)))
    (fun _ => (k:ℤ))
    (entryOrder.map (fun m => EntryEvent.mk (memberRecord m)
      (label (familyCreator (memberFamily m)) (memberJoin m)) (origin m)))

variable {Record Good Boundary Bad Member RootBlock Block Paid Ordinary}

abbrev Trace (k : ℕ) := AccountingTrace Record Good Boundary Bad Member RootBlock Block Paid Ordinary k

namespace AccountingTrace

def rows {k : ℕ} (s : Trace (Record:=Record) (Good:=Good) (Boundary:=Boundary) (Bad:=Bad)
    (Member:=Member) (RootBlock:=RootBlock) (Block:=Block) (Paid:=Paid) (Ordinary:=Ordinary) k) :=
  s.entryOrder.map (fun m => EntryEvent.mk (s.memberRecord m)
    (s.label (s.familyCreator (s.memberFamily m)) (s.memberJoin m)) (s.origin m))

variable {k : ℕ} (s : Trace (Record:=Record) (Good:=Good) (Boundary:=Boundary) (Bad:=Bad)
  (Member:=Member) (RootBlock:=RootBlock) (Block:=Block) (Paid:=Paid) (Ordinary:=Ordinary) k)

def positive : ℤ := ∑ cell : Record × Fin s.time, max 0 (labelDelta s.time s.label cell)
def negative : ℤ := ∑ cell : Record × Fin s.time, max 0 (-labelDelta s.time s.label cell)
def exceptions : ℤ := entryExceptions s.rows

theorem exception_census : s.exceptions =
    ∑ m, (if (s.origin m).isNone then (1 : ℤ) else 0) := by
  exact entry_exception_census s.entryOrder _ s.orderNodup s.orderComplete

theorem exception_bound : s.exceptions ≤
    (Fintype.card Record : ℤ) + (Fintype.card Ordinary : ℤ) +
      (Fintype.card Good : ℤ) + (Fintype.card Boundary : ℤ) := by
  have hc := Fintype.card_le_of_injective s.exceptionalOrigin s.exceptionalInjective
  have hci : (Fintype.card {m // (s.origin m).isNone} : ℤ) ≤
      (Fintype.card (Sum Record (Sum Ordinary (Sum Good Boundary))) : ℤ) := by
    exact_mod_cast hc
  rw [s.exception_census, Finset.sum_boole]
  simpa [Fintype.card_subtype, Fintype.card_sum, add_assoc] using hci

theorem positive_bound (hk : 1 ≤ k) :
    s.positive ≤ 4 * (Fintype.card Block : ℤ) * ((k:ℤ)-1) +
      (Fintype.card Paid : ℤ) * (k:ℤ) := by
  classical
  have hcapacity : ∀ b, Fintype.card {e // s.positiveOrigin e = Sum.inl b} ≤ 4 := by
    intro b
    have h := (s.positiveHistory b).bound
    rw [sum_stage_counts] at h
    simpa [Fintype.card_subtype] using h
  obtain ⟨charge, hinj, _⟩ := exists_sum_slots s.positiveOrigin 4 hcapacity s.positivePaidUnique
  apply positive_variation_slots (labelDelta s.time s.label) (k:ℤ)
    (by exact_mod_cast hk) _ charge hinj
  intro cell
  have hbefore := (s.labelBounds cell.1 cell.2.val (Nat.le_of_lt cell.2.isLt)).1
  have hafter := (s.labelBounds cell.1 (cell.2.val+1) cell.2.isLt).2
  unfold labelDelta
  omega

theorem negative_bound : s.negative ≤
    (Fintype.card Record : ℤ) * ((k:ℤ)-1) + s.positive := by
  exact finite_label_variation_balance s.time s.label (k:ℤ)
    (fun v => (s.labelBounds v 0 (Nat.zero_le _)).2)
    (fun v => (s.labelBounds v s.time (le_refl _)).1)

theorem good_bound : (Fintype.card Good : ℤ) ≤ s.negative :=
  negative_variation_slots (labelDelta s.time s.label) s.goodCell s.goodInjective s.goodDrop

theorem boundary_bound (hk : 1 ≤ k) : (Fintype.card Boundary : ℤ) ≤
    s.negative + (2*(k:ℤ)+4) * (Fintype.card Block : ℤ) := by
  classical
  have hcapacity : ∀ b, Fintype.card {e // s.boundaryOrigin e = Sum.inl b} ≤ 2*k+4 := by
    intro b
    have h := (s.boundaryHistory b).bound hk
    rw [sum_stage_counts] at h
    simpa [Fintype.card_subtype, add_assoc] using h
  obtain ⟨charge, hinj, hframe⟩ :=
    exists_sum_slots s.boundaryOrigin (2*k+4) hcapacity s.boundaryDropUnique
  apply boundary_variation_slots (labelDelta s.time s.label) k
    (fun e => (charge e).swap)
    (fun a b h => hinj (by simpa using congrArg Sum.swap h))
  intro e cell he
  apply s.boundaryDrop e cell
  have hc : charge e = Sum.inr cell := by
    simpa using congrArg Sum.swap he
  simpa [hc] using (hframe e).symm

theorem member_overlap (v : Record) (t : ℕ) :
    (∑ m, if s.memberRecord m = v ∧ s.memberJoin m ≤ t ∧ t < s.memberEnd m then (1:ℤ) else 0) ≤ 1 := by
  classical
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter (fun m => s.memberRecord m = v ∧
      s.memberJoin m ≤ t ∧ t < s.memberEnd m)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact s.oneMembership v t a b ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2
  exact_mod_cast hc

theorem creator_overlap (v : Record) (t : ℕ) :
    (∑ b, if s.familyCreator b = v ∧ s.growthStart b ≤ t ∧ t < s.growthEnd b then (1:ℤ) else 0) ≤ 3 := by
  classical
  let active := {b // s.familyCreator b = v ∧ s.growthStart b ≤ t ∧ t < s.growthEnd b}
  have hi : Function.Injective (fun b : active => s.growthSlot b.val) := by
    intro a b hab
    apply Subtype.ext
    exact s.oneGrowthSlot v t a.val b.val a.property.1 a.property.2.1 a.property.2.2
      b.property.1 b.property.2.1 b.property.2.2 hab
  have hc := Fintype.card_le_of_injective _ hi
  have hci : (Fintype.card active : ℤ) ≤ 3 := by exact_mod_cast hc
  rw [Finset.sum_boole]
  simpa [active, Fintype.card_subtype] using hci

theorem winner_capacity (m : Member) :
    (Finset.univ.filter (fun e => s.winnerEntry e = m)).card ≤ 4 := by
  have h := (s.winnerHistory m).bound
  rw [sum_stage_counts] at h
  exact h

theorem cut_capacity (hk : 1 ≤ k) (b : RootBlock) (t : ℕ) :
    (∑ e, if s.memberFamily (s.winnerEntry e) = b ∧
      min (s.memberJoin (s.winnerEntry e)) (s.memberJoin (s.loserEntry e)) ≤ t ∧
      t < max (s.memberJoin (s.winnerEntry e)) (s.memberJoin (s.loserEntry e)) then (1:ℤ) else 0) ≤
        (k:ℤ)+1 := by
  rw [Finset.sum_boole]
  have h := (s.cutHistory b t).bound hk
  rw [sum_stage_counts] at h
  exact_mod_cast h

def entryRank (m : Member) : ℤ :=
  s.label (s.memberRecord m) (s.memberJoin m) -
    s.label (s.familyCreator (s.memberFamily m)) (s.memberJoin m)

def winnerShift (e : Bad) : ℤ :=
  s.label (s.memberRecord (s.winnerEntry e)) (s.memberJoin (s.winnerEntry e)) -
    s.label (s.memberRecord (s.winnerEntry e)) (s.linkTime e)

def loserShift (e : Bad) : ℤ :=
  s.label (s.memberRecord (s.winnerEntry e)) (s.linkTime e) -
    s.label (s.familyCreator (s.memberFamily (s.loserEntry e))) (s.memberJoin (s.loserEntry e))

def creatorShift (e : Bad) : ℤ :=
  s.label (s.familyCreator (s.memberFamily (s.winnerEntry e))) (s.memberJoin (s.loserEntry e)) -
    s.label (s.familyCreator (s.memberFamily (s.winnerEntry e))) (s.memberJoin (s.winnerEntry e))

theorem entryRank_shifts (e : Bad) :
    s.entryRank (s.winnerEntry e) = s.winnerShift e + s.loserShift e + s.creatorShift e := by
  unfold entryRank winnerShift loserShift creatorShift
  rw [s.sameFamily e]
  ring

theorem winner_shift_bound : (∑ e, s.winnerShift e) ≤ 4 * s.negative := by
  apply global_winner_shift_bound s.winnerEntry s.memberRecord s.memberJoin s.memberEnd
    s.linkTime s.label s.time 4 (by norm_num) (fun m => (s.memberTimes m).2) s.winnerTimes
  · intro m
    rw [Finset.sum_boole]
    exact_mod_cast s.winner_capacity m
  · exact s.member_overlap

theorem loser_shift_bound (hk : 1 ≤ k) :
    (∑ e, s.loserShift e) ≤ ((k:ℤ)-1) * s.exceptions := by
  have h := entry_loser_bound (k:ℤ) s.loserShift s.rows (by exact_mod_cast hk) s.entryLedger
  rw [sum_map_full_census (entryBadEdges s.rows) s.loserShift s.badNodup s.badComplete] at h
  simpa only [exceptions, mul_comm] using h

theorem creator_shift_bound (hk : 1 ≤ k) : (∑ e, s.creatorShift e) ≤
    3 * ((k:ℤ)+1) * (s.positive + s.negative) := by
  have hj : ∀ e,
      (s.growthStart (s.memberFamily (s.winnerEntry e)) ≤ s.memberJoin (s.winnerEntry e) ∧
        s.memberJoin (s.winnerEntry e) ≤ s.growthEnd (s.memberFamily (s.winnerEntry e))) ∧
      (s.growthStart (s.memberFamily (s.winnerEntry e)) ≤ s.memberJoin (s.loserEntry e) ∧
        s.memberJoin (s.loserEntry e) ≤ s.growthEnd (s.memberFamily (s.winnerEntry e))) := by
    intro e
    exact ⟨s.entryInGrowth (s.winnerEntry e),
      by simpa only [s.sameFamily e] using s.entryInGrowth (s.loserEntry e)⟩
  have h := global_creator_shift_bound (fun e => s.memberFamily (s.winnerEntry e))
    s.familyCreator s.growthStart s.growthEnd
    (fun e => s.memberJoin (s.winnerEntry e)) (fun e => s.memberJoin (s.loserEntry e))
    s.label s.time 3 ((k:ℤ)+1) (by positivity) s.growthFinish hj (s.cut_capacity hk) s.creator_overlap
  have habs : (∑ cell : Record × Fin s.time, |labelDelta s.time s.label cell|) =
      s.positive + s.negative := by
    unfold positive negative
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro cell hc
    by_cases hd : 0 ≤ labelDelta s.time s.label cell
    · rw [abs_of_nonneg hd, max_eq_right hd, max_eq_left (by omega)]
      ring
    · have hn : labelDelta s.time s.label cell ≤ 0 := by omega
      rw [abs_of_nonpos hn, max_eq_left hn, max_eq_right (by omega)]
      ring
  rw [habs] at h
  exact h

theorem bad_bound (hk : 1 ≤ k) : (Fintype.card Bad : ℤ) ≤
    (5*(k:ℤ)-1) * s.exceptions + 4*s.negative +
      3*((k:ℤ)+1)*(s.positive+s.negative) := by
  have hlabels : ∀ m,
      1 ≤ s.label (s.memberRecord m) (s.memberJoin m) ∧
      s.label (s.familyCreator (s.memberFamily m)) (s.memberJoin m) ≤ (k:ℤ) := by
    intro m
    have htime := (s.memberTimes m).1.trans (s.memberTimes m).2
    exact ⟨(s.labelBounds _ _ htime).1, (s.labelBounds _ _ htime).2⟩
  have hstrict : ∀ m, (s.origin m).isNone = false →
      s.label (s.familyCreator (s.memberFamily m)) (s.memberJoin m) + 1 ≤
        s.label (s.memberRecord m) (s.memberJoin m) := by
    intro m hm
    cases ho : s.origin m with
    | none => simp [ho] at hm
    | some e => exact s.badEntryStrict m (by simp [ho])
  have hbad := bad_activity_from_entries s.winnerEntry
    (fun m => s.label (s.memberRecord m) (s.memberJoin m))
    (fun m => s.label (s.familyCreator (s.memberFamily m)) (s.memberJoin m))
    (fun m => (s.origin m).isNone) (k:ℤ) 4 (by exact_mod_cast hk)
    hlabels hstrict s.winner_capacity
  change (Fintype.card Bad : ℤ) ≤ (∑ e, s.entryRank (s.winnerEntry e)) +
    (4:ℤ)*(k:ℤ)*(∑ m, if (s.origin m).isNone then (1:ℤ) else 0) at hbad
  rw [← s.exception_census] at hbad
  simp_rw [s.entryRank_shifts] at hbad
  simp only [Finset.sum_add_distrib] at hbad
  have hv := s.winner_shift_bound
  have hw := s.loser_shift_bound hk
  have hu := s.creator_shift_bound hk
  nlinarith

include s

/-- The complete finite-trace accounting theorem. All shift sums,
potential-variation inequalities, and exceptional-entry totals used by
the numerical closure are derived from the local trace interface. -/
theorem activity_le_quadratic (hk : 2 ≤ k) :
    Fintype.card Good + Fintype.card Boundary + Fintype.card Bad ≤
      74 * (Fintype.card Record + Fintype.card Ordinary +
        Fintype.card Block + Fintype.card Paid) * k^2 := by
  have hk1 : 1 ≤ k := by omega
  have hki : 2 ≤ (k:ℤ) := by exact_mod_cast hk
  have hp := s.positive_bound hk1
  have hm := s.negative_bound
  have hg := s.good_bound
  have hb := s.boundary_bound (by omega)
  have he := s.exception_bound
  have ha := s.bad_bound hk1
  have hentries : s.exceptions ≤ (Fintype.card Record : ℤ) + (Fintype.card Ordinary : ℤ) +
      2*s.negative + (2*(k:ℤ)+4)*(Fintype.card Block : ℤ) := by linarith
  have hledger : (Fintype.card Bad : ℤ) + (Fintype.card Good : ℤ) + (Fintype.card Boundary : ℤ) ≤
      (5*(k:ℤ)-1)*s.exceptions + 6*s.negative +
        3*((k:ℤ)+1)*(s.positive+s.negative) + (2*(k:ℤ)+4)*(Fintype.card Block : ℤ) := by
    linarith
  have h := quantitative_quadratic (k:ℤ) (Fintype.card Record : ℤ)
    (Fintype.card Block : ℤ) (Fintype.card Paid : ℤ) (Fintype.card Ordinary : ℤ)
    s.positive s.negative s.exceptions
    ((Fintype.card Bad : ℤ) + (Fintype.card Good : ℤ) + (Fintype.card Boundary : ℤ))
    hki (by positivity) (by positivity) (by positivity) (by positivity)
    hp hm hentries hledger
  have hnat : Fintype.card Bad + Fintype.card Good + Fintype.card Boundary ≤
      74 * (Fintype.card Record + Fintype.card Ordinary +
        Fintype.card Block + Fintype.card Paid) * k^2 := by exact_mod_cast h
  simpa only [add_assoc, add_comm, add_left_comm] using hnat

end AccountingTrace
end GreedyForest.Execution
