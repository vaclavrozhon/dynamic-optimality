import Mathlib

/-!
Signed block-membership ledgers for complete Cartesian consolidations.
This file formalizes the history algebra only. The BST representation,
cut multiplicities, and complete-consolidation hypotheses are separate.
-/
namespace GreedyForest

/-- A transition records whether it is an internal bad transfer and the
creator label at entry to the next root-block family. -/
abbrev Transition := Bool × ℤ

def badShiftSum (current : ℤ) : List Transition → ℤ
  | [] => 0
  | (bad, next) :: rest =>
      (if bad then next - current else 0) + badShiftSum next rest

def exceptions : List Transition → ℕ
  | [] => 0
  | (bad, _) :: rest => (if bad then 0 else 1) + exceptions rest

def labelsBounded (K : ℤ) (steps : List Transition) : Prop :=
  ∀ step ∈ steps, 1 ≤ step.2 ∧ step.2 ≤ K

/-- A marked history telescopes across bad transfers. Each exceptional
transition starts a new run; no absolute-value charge per bad link is used. -/
theorem badShiftSum_le_remaining (K current : ℤ) (steps : List Transition)
    (hcurrent : 1 ≤ current ∧ current ≤ K)
    (hsteps : labelsBounded K steps) :
    badShiftSum current steps ≤
      K - current + (exceptions steps : ℤ) * (K - 1) := by
  induction steps generalizing current with
  | nil => simp [badShiftSum, exceptions]; omega
  | cons step rest ih =>
      rcases step with ⟨bad, next⟩
      have hnext : 1 ≤ next ∧ next ≤ K := hsteps (bad, next) (by simp)
      have hrest : labelsBounded K rest := by
        intro e he
        exact hsteps e (by simp [he])
      have htail := ih next hnext hrest
      cases bad <;> simp only [badShiftSum, exceptions, Bool.false_eq_true,
        ↓reduceIte, Nat.cast_add, Nat.cast_one, Nat.cast_zero] at *
      · nlinarith
      · nlinarith

/-- The familiar bound by number of maximal bad-transfer runs follows
from the stronger remaining-potential inequality. -/
theorem badShiftSum_le_runs (K current : ℤ) (steps : List Transition)
    (hcurrent : 1 ≤ current ∧ current ≤ K)
    (hsteps : labelsBounded K steps) :
    badShiftSum current steps ≤
      ((exceptions steps : ℤ) + 1) * (K - 1) := by
  have h := badShiftSum_le_remaining K current steps hcurrent hsteps
  nlinarith

/-- Exact entry deficit. It covers a creator label greater than the
new member's label, rather than silently assuming all entries are strict. -/
def entryDeficit (member creator : ℤ) : ℤ := max 0 (1 - (member - creator))

theorem entryRank_add_deficit (member creator : ℤ) :
    1 ≤ (member - creator) + entryDeficit member creator := by
  unfold entryDeficit
  have h := le_max_right (0 : ℤ) (1 - (member - creator))
  omega

theorem entryDeficit_nonneg (member creator : ℤ) :
    0 ≤ entryDeficit member creator := le_max_left _ _

theorem entryDeficit_eq_zero_of_strict (member creator : ℤ)
    (hstrict : creator + 1 ≤ member) :
    entryDeficit member creator = 0 := by
  unfold entryDeficit
  exact max_eq_left (by omega)

theorem entryDeficit_le_bound (K member creator : ℤ)
    (hK : 1 ≤ K) (hm : 1 ≤ member) (hc : creator ≤ K) :
    entryDeficit member creator ≤ K := by
  unfold entryDeficit
  exact max_le (by omega) (by omega)

/-- One root-block-family membership, including its eventual internal wins. -/
structure Membership where
  memberLabel : ℤ
  creatorLabel : ℤ
  internalWins : ℕ
  exceptional : Bool

def pairRanks (m : Membership) : ℤ :=
  (m.internalWins : ℤ) * (m.memberLabel - m.creatorLabel)

def deficitCharge (m : Membership) : ℤ :=
  (m.internalWins : ℤ) * entryDeficit m.memberLabel m.creatorLabel

/-- Summing pair ranks is valid even when some historical entry ranks
are zero or negative. The deficit is charged once per bounded-capacity win. -/
theorem membership_activity_le (m : Membership) :
    (m.internalWins : ℤ) ≤ pairRanks m + deficitCharge m := by
  have h := entryRank_add_deficit m.memberLabel m.creatorLabel
  have hn : 0 ≤ (m.internalWins : ℤ) := by positivity
  unfold pairRanks deficitCharge
  nlinarith

theorem deficitCharge_le_exception (K : ℤ) (D : ℕ) (m : Membership)
    (hK : 1 ≤ K)
    (hm : 1 ≤ m.memberLabel) (hc : m.creatorLabel ≤ K)
    (hwins : m.internalWins ≤ D)
    (hstrict : m.exceptional = false → m.creatorLabel + 1 ≤ m.memberLabel) :
    deficitCharge m ≤ if m.exceptional then (D : ℤ) * K else 0 := by
  cases hflag : m.exceptional
  · have hz := entryDeficit_eq_zero_of_strict m.memberLabel m.creatorLabel
      (hstrict hflag)
    simp [deficitCharge, hz]
  · have hd := entryDeficit_le_bound K m.memberLabel m.creatorLabel hK hm hc
    have hn : 0 ≤ (m.internalWins : ℤ) := by positivity
    have hcast : (m.internalWins : ℤ) ≤ (D : ℤ) := by exact_mod_cast hwins
    have hdn := entryDeficit_nonneg m.memberLabel m.creatorLabel
    simp only [↓reduceIte]
    unfold deficitCharge
    nlinarith

/-- The three signed shifts are an exact identity, independent of the
ordering of the two historical joins. -/
theorem three_shift_identity (winnerAtJoin creatorAtWinnerJoin
    winnerNow creatorAtLoserJoin : ℤ) :
    winnerAtJoin - creatorAtWinnerJoin =
      (winnerAtJoin - winnerNow) +
      (winnerNow - creatorAtLoserJoin) +
      (creatorAtLoserJoin - creatorAtWinnerJoin) := by ring

/-- The bounded-membership condition is local to each entry. It does not
assume that the aggregate activity is small. -/
def validMembership (K : ℤ) (D : ℕ) (m : Membership) : Prop :=
  1 ≤ m.memberLabel ∧ m.memberLabel ≤ K ∧
  1 ≤ m.creatorLabel ∧ m.creatorLabel ≤ K ∧
  m.internalWins ≤ D ∧
  (m.exceptional = false → m.creatorLabel + 1 ≤ m.memberLabel)

def exceptionalCount : List Membership → ℕ
  | [] => 0
  | m :: rest => (if m.exceptional then 1 else 0) + exceptionalCount rest

theorem activity_le_rankMass_deficits (entries : List Membership) :
    (entries.map (fun m => (m.internalWins : ℤ))).sum ≤
      (entries.map pairRanks).sum + (entries.map deficitCharge).sum := by
  induction entries with
  | nil => simp
  | cons m rest ih =>
      have hm := membership_activity_le m
      simp only [List.map_cons, List.sum_cons]
      linarith

theorem deficitMass_le_exceptions (K : ℤ) (D : ℕ) (entries : List Membership)
    (hK : 1 ≤ K)
    (hvalid : ∀ m ∈ entries, validMembership K D m) :
    (entries.map deficitCharge).sum ≤
      (D : ℤ) * K * (exceptionalCount entries : ℤ) := by
  induction entries with
  | nil => simp [exceptionalCount]
  | cons m rest ih =>
      have hm := hvalid m (by simp)
      have hrest : ∀ z ∈ rest, validMembership K D z := by
        intro z hz
        exact hvalid z (by simp [hz])
      have htail := ih hrest
      have hhead := deficitCharge_le_exception K D m hK hm.1 hm.2.2.2.1
        hm.2.2.2.2.1 hm.2.2.2.2.2
      cases hflag : m.exceptional <;>
        simp [exceptionalCount, hflag] at hhead ⊢ <;> nlinarith

/-- Global entry-deficit activity inequality, derived from local entry
labels and capacities rather than posited as an amortization assumption. -/
theorem activity_le_rankMass_exceptions (K : ℤ) (D : ℕ)
    (entries : List Membership) (hK : 1 ≤ K)
    (hvalid : ∀ m ∈ entries, validMembership K D m) :
    (entries.map (fun m => (m.internalWins : ℤ))).sum ≤
      (entries.map pairRanks).sum +
      (D : ℤ) * K * (exceptionalCount entries : ℤ) := by
  have h₁ := activity_le_rankMass_deficits entries
  have h₂ := deficitMass_le_exceptions K D entries hK hvalid
  linarith

structure MembershipHistory where
  firstCreator : ℤ
  transitions : List Transition

def historyShift (h : MembershipHistory) : ℤ :=
  badShiftSum h.firstCreator h.transitions

def historyRuns (h : MembershipHistory) : ℕ :=
  exceptions h.transitions + 1

theorem historySum_le_runCount (K : ℤ) (histories : List MembershipHistory)
    (hbound : ∀ h ∈ histories,
      (1 ≤ h.firstCreator ∧ h.firstCreator ≤ K) ∧ labelsBounded K h.transitions) :
    (histories.map historyShift).sum ≤
      ((histories.map historyRuns).sum : ℤ) * (K - 1) := by
  induction histories with
  | nil => simp
  | cons h rest ih =>
      have hb := hbound h (by simp)
      have hr : ∀ z ∈ rest,
          (1 ≤ z.firstCreator ∧ z.firstCreator ≤ K) ∧ labelsBounded K z.transitions := by
        intro z hz
        exact hbound z (by simp [hz])
      have htail := ih hr
      have hhead := badShiftSum_le_runs K h.firstCreator h.transitions hb.1 hb.2
      have hhead' : historyShift h ≤ (historyRuns h : ℤ) * (K - 1) := by
        simpa [historyShift, historyRuns] using hhead
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      nlinarith

open scoped BigOperators

/-- A historical label difference is exactly the signed sum of its
underlying changes, including all intermediate oscillations. -/
theorem telescoping_interval (f : ℕ → ℤ) (s t : ℕ) (hst : s ≤ t) :
    ∑ i ∈ Finset.Ico s t, (f (i + 1) - f i) = f t - f s := by
  rw [Finset.sum_Ico_eq_sub _ hst, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- Double-counting signed historical intervals: an event covered with
total absolute multiplicity at most M pays at most M times its variation. -/
theorem signed_coverage_bound {Edge Time : Type*} [Fintype Edge] [Fintype Time]
    (coefficient : Edge → Time → ℤ) (delta : Time → ℤ) (M : ℤ)
    (hmult : ∀ t, ∑ e, |coefficient e t| ≤ M) :
    ∑ e, ∑ t, coefficient e t * delta t ≤ M * ∑ t, |delta t| := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    ∑ e, coefficient e t * delta t ≤ ∑ e, |coefficient e t| * |delta t| := by
      apply Finset.sum_le_sum
      intro e he
      calc
        coefficient e t * delta t ≤ |coefficient e t * delta t| := le_abs_self _
        _ = |coefficient e t| * |delta t| := abs_mul _ _
    _ = (∑ e, |coefficient e t|) * |delta t| := by rw [Finset.sum_mul]
    _ ≤ M * |delta t| := mul_le_mul_of_nonneg_right (hmult t) (abs_nonneg _)

/-- Winner shifts need only negative variation, since their historical
intervals all have the same orientation. -/
theorem winner_coverage_bound {Edge Time : Type*} [Fintype Edge] [Fintype Time]
    (coefficient : Edge → Time → ℤ) (delta : Time → ℤ) (D : ℤ)
    (hnonneg : ∀ e t, 0 ≤ coefficient e t)
    (hmult : ∀ t, ∑ e, coefficient e t ≤ D) :
    ∑ e, ∑ t, coefficient e t * (-delta t) ≤
      D * ∑ t, max 0 (-delta t) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  calc
    ∑ e, coefficient e t * (-delta t) = (∑ e, coefficient e t) * (-delta t) := by
      rw [Finset.sum_mul]
    _ ≤ (∑ e, coefficient e t) * max 0 (-delta t) := by
      apply mul_le_mul_of_nonneg_left (le_max_right _ _)
      exact Finset.sum_nonneg (fun e _ => hnonneg e t)
    _ ≤ D * max 0 (-delta t) :=
      mul_le_mul_of_nonneg_right (hmult t) (le_max_left _ _)

/-- Coefficient of one actual label change in a signed difference of
two historical entry snapshots. -/
def joinCoefficient (winnerJoin loserJoin time : ℕ) : ℤ :=
  (if time < loserJoin then 1 else 0) - (if time < winnerJoin then 1 else 0)

theorem joinCoefficient_abs (winnerJoin loserJoin time : ℕ) :
    |joinCoefficient winnerJoin loserJoin time| =
      if min winnerJoin loserJoin ≤ time ∧ time < max winnerJoin loserJoin
      then 1 else 0 := by
  unfold joinCoefficient
  by_cases hw : time < winnerJoin <;> by_cases hl : time < loserJoin <;>
    simp [hw, hl]

theorem joinCoefficient_zero_outside_growth (start finish winnerJoin loserJoin time : ℕ)
    (hw : start ≤ winnerJoin ∧ winnerJoin ≤ finish)
    (hl : start ≤ loserJoin ∧ loserJoin ≤ finish)
    (hout : ¬ (start ≤ time ∧ time < finish)) :
    joinCoefficient winnerJoin loserJoin time = 0 := by
  unfold joinCoefficient
  by_cases ht : time < start
  · have htw : time < winnerJoin := by omega
    have htl : time < loserJoin := by omega
    simp [htw, htl]
  · have htw : ¬ time < winnerJoin := by omega
    have htl : ¬ time < loserJoin := by omega
    simp [htw, htl]

theorem prefix_sum_range (T join : ℕ) (g : ℕ → ℤ) (hjoin : join ≤ T) :
    ∑ t ∈ Finset.range T, (if t < join then g t else 0) =
      ∑ t ∈ Finset.range join, g t := by
  have hfilter : (Finset.range T).filter (fun t => t < join) = Finset.range join := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]

/-- Historical snapshots are expanded into actual intervening changes;
the two joins may occur in either order. -/
theorem joinCoefficient_telescope (f : ℕ → ℤ) (T winnerJoin loserJoin : ℕ)
    (hw : winnerJoin ≤ T) (hl : loserJoin ≤ T) :
    ∑ t ∈ Finset.range T,
      joinCoefficient winnerJoin loserJoin t * (f (t + 1) - f t) =
        f loserJoin - f winnerJoin := by
  unfold joinCoefficient
  simp_rw [sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, prefix_sum_range T loserJoin _ hl,
    prefix_sum_range T winnerJoin _ hw, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- Local per-family cut capacities and simultaneous growth overlap
imply the creator-change multiplicity bound. No aggregate multiplicity
inequality is assumed: coefficients come from the two actual join times. -/
theorem creator_join_multiplicity {Block Edge : Type*} [Fintype Block] [Fintype Edge]
    [DecidableEq Block]
    (family : Edge → Block) (start finish : Block → ℕ)
    (winnerJoin loserJoin : Edge → ℕ) (time : ℕ) (C M : ℤ)
    (hM : 0 ≤ M)
    (hjoins : ∀ e,
      (start (family e) ≤ winnerJoin e ∧ winnerJoin e ≤ finish (family e)) ∧
      (start (family e) ≤ loserJoin e ∧ loserJoin e ≤ finish (family e)))
    (hlocal : ∀ b,
      ∑ e, (if family e = b ∧
        min (winnerJoin e) (loserJoin e) ≤ time ∧
          time < max (winnerJoin e) (loserJoin e) then (1 : ℤ) else 0) ≤ M)
    (hoverlap : ∑ b, (if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) ≤ C) :
    ∑ e, |joinCoefficient (winnerJoin e) (loserJoin e) time| ≤ C * M := by
  classical
  let mass : Block → ℤ := fun b =>
    ∑ e, if family e = b then |joinCoefficient (winnerJoin e) (loserJoin e) time| else 0
  have hsum : ∑ b, mass b =
      ∑ e, |joinCoefficient (winnerJoin e) (loserJoin e) time| := by
    dsimp [mass]
    rw [Finset.sum_comm]
    simp
  have hmass : ∀ b, mass b ≤
      (if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * M := by
    intro b
    by_cases hactive : start b ≤ time ∧ time < finish b
    · have heq : mass b = ∑ e, (if family e = b ∧
          min (winnerJoin e) (loserJoin e) ≤ time ∧
            time < max (winnerJoin e) (loserJoin e) then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [joinCoefficient_abs]
        by_cases hf : family e = b <;> simp [hf]
      simpa only [heq, if_pos hactive, one_mul] using hlocal b
    · have hz : mass b = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        by_cases hf : family e = b
        · have hj := hjoins e
          have hzero := joinCoefficient_zero_outside_growth
            (start b) (finish b) (winnerJoin e) (loserJoin e) time
            (by simpa [hf] using hj.1) (by simpa [hf] using hj.2) hactive
          simp [hf, hzero]
        · simp [hf]
      simp [hactive, hz]
  rw [← hsum]
  calc
    ∑ b, mass b ≤ ∑ b, (if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * M :=
      Finset.sum_le_sum (fun b _ => hmass b)
    _ = (∑ b, if start b ≤ time ∧ time < finish b then (1 : ℤ) else 0) * M := by
      rw [Finset.sum_mul]
    _ ≤ C * M := mul_le_mul_of_nonneg_right hoverlap hM

/-- Creator shifts from actual membership entry times are bounded by
growth overlap times local cut capacity times actual creator variation. -/
theorem creator_join_shift_bound {Block Edge : Type*} [Fintype Block] [Fintype Edge]
    [DecidableEq Block] (family : Edge → Block) (start finish : Block → ℕ)
    (winnerJoin loserJoin : Edge → ℕ) (f : ℕ → ℤ) (T : ℕ) (C M : ℤ)
    (hM : 0 ≤ M) (hfinish : ∀ b, finish b ≤ T)
    (hjoins : ∀ e,
      (start (family e) ≤ winnerJoin e ∧ winnerJoin e ≤ finish (family e)) ∧
      (start (family e) ≤ loserJoin e ∧ loserJoin e ≤ finish (family e)))
    (hlocal : ∀ b t,
      ∑ e, (if family e = b ∧
        min (winnerJoin e) (loserJoin e) ≤ t ∧
          t < max (winnerJoin e) (loserJoin e) then (1 : ℤ) else 0) ≤ M)
    (hoverlap : ∀ t,
      ∑ b, (if start b ≤ t ∧ t < finish b then (1 : ℤ) else 0) ≤ C) :
    ∑ e, (f (loserJoin e) - f (winnerJoin e)) ≤
      C * M * ∑ t ∈ Finset.range T, |f (t + 1) - f t| := by
  classical
  have hexpand : ∑ e, (f (loserJoin e) - f (winnerJoin e)) =
      ∑ e, ∑ t ∈ Finset.range T,
        joinCoefficient (winnerJoin e) (loserJoin e) t * (f (t + 1) - f t) := by
    apply Finset.sum_congr rfl
    intro e he
    exact (joinCoefficient_telescope f T (winnerJoin e) (loserJoin e)
      ((hjoins e).1.2.trans (hfinish _)) ((hjoins e).2.2.trans (hfinish _))).symm
  rw [hexpand, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have hmult := creator_join_multiplicity family start finish winnerJoin loserJoin t C M
    hM hjoins (fun b => hlocal b t) (hoverlap t)
  calc
    ∑ e, joinCoefficient (winnerJoin e) (loserJoin e) t * (f (t + 1) - f t)
        ≤ ∑ e, |joinCoefficient (winnerJoin e) (loserJoin e) t| * |f (t + 1) - f t| := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ |joinCoefficient (winnerJoin e) (loserJoin e) t * (f (t + 1) - f t)| := le_abs_self _
        _ = _ := abs_mul _ _
    _ = (∑ e, |joinCoefficient (winnerJoin e) (loserJoin e) t|) * |f (t + 1) - f t| := by
      rw [Finset.sum_mul]
    _ ≤ (C * M) * |f (t + 1) - f t| :=
      mul_le_mul_of_nonneg_right hmult (abs_nonneg _)

theorem joinCoefficient_nonneg_ordered (join link time : ℕ) (h : join ≤ link) :
    0 ≤ joinCoefficient join link time := by
  unfold joinCoefficient
  by_cases hj : time < join <;> by_cases hl : time < link
  all_goals simp [hj, hl]
  omega

/-- For one winner record, membership intervals do not overlap and each
membership permits at most D internal wins. Its historical winner shifts
therefore charge only negative actual label variation, with multiplicity D. -/
theorem winner_join_shift_bound {Membership Edge : Type*}
    [Fintype Membership] [Fintype Edge] [DecidableEq Membership]
    (membership : Edge → Membership) (join finish : Membership → ℕ)
    (linkTime : Edge → ℕ) (f : ℕ → ℤ) (T : ℕ) (D : ℤ)
    (hD : 0 ≤ D) (hfinish : ∀ b, finish b ≤ T)
    (htimes : ∀ e, join (membership e) ≤ linkTime e ∧ linkTime e ≤ finish (membership e))
    (hcapacity : ∀ b, ∑ e, (if membership e = b then (1 : ℤ) else 0) ≤ D)
    (hoverlap : ∀ t,
      ∑ b, (if join b ≤ t ∧ t < finish b then (1 : ℤ) else 0) ≤ 1) :
    ∑ e, (f (join (membership e)) - f (linkTime e)) ≤
      D * ∑ t ∈ Finset.range T, max 0 (f t - f (t + 1)) := by
  classical
  have hlocal : ∀ b t,
      ∑ e, (if membership e = b ∧
        min (join (membership e)) (linkTime e) ≤ t ∧
          t < max (join (membership e)) (linkTime e) then (1 : ℤ) else 0) ≤ D := by
    intro b t
    calc
      _ ≤ ∑ e, (if membership e = b then (1 : ℤ) else 0) := by
        apply Finset.sum_le_sum
        intro e he
        split_ifs <;> simp_all
      _ ≤ D := hcapacity b
  have hmult : ∀ t, ∑ e, joinCoefficient (join (membership e)) (linkTime e) t ≤ D := by
    intro t
    have hh := creator_join_multiplicity membership join finish
      (fun e => join (membership e)) linkTime t 1 D hD
      (fun e => ⟨⟨le_refl _, (htimes e).1.trans (htimes e).2⟩, htimes e⟩)
      (fun b => hlocal b t) (hoverlap t)
    simp only [one_mul] at hh
    simpa only [abs_of_nonneg (joinCoefficient_nonneg_ordered _ _ t (htimes _).1)] using hh
  have hexpand : ∑ e, (f (join (membership e)) - f (linkTime e)) =
      ∑ e, ∑ t ∈ Finset.range T,
        joinCoefficient (join (membership e)) (linkTime e) t * (f t - f (t + 1)) := by
    apply Finset.sum_congr rfl
    intro e he
    have htel := joinCoefficient_telescope f T (join (membership e)) (linkTime e)
      ((htimes e).1.trans ((htimes e).2.trans (hfinish _)))
      ((htimes e).2.trans (hfinish _))
    have hneg : ∑ t ∈ Finset.range T,
        joinCoefficient (join (membership e)) (linkTime e) t * (f t - f (t + 1)) =
          -(∑ t ∈ Finset.range T,
            joinCoefficient (join (membership e)) (linkTime e) t * (f (t + 1) - f t)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    rw [hneg, htel]
    ring
  rw [hexpand, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  rw [← Finset.sum_mul]
  have hnonneg : 0 ≤ ∑ e, joinCoefficient (join (membership e)) (linkTime e) t :=
    Finset.sum_nonneg (fun e _ => joinCoefficient_nonneg_ordered _ _ t (htimes e).1)
  calc
    _ ≤ (∑ e, joinCoefficient (join (membership e)) (linkTime e) t) *
        max 0 (f t - f (t + 1)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hnonneg
    _ ≤ D * max 0 (f t - f (t + 1)) :=
      mul_le_mul_of_nonneg_right (hmult t) (le_max_left _ _)

def positiveVariation (f : ℕ → ℤ) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, max 0 (f (t + 1) - f t)

def negativeVariation (f : ℕ → ℤ) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T, max 0 (f t - f (t + 1))

theorem variation_balance (f : ℕ → ℤ) (T : ℕ) :
    positiveVariation f T - negativeVariation f T = f T - f 0 := by
  unfold positiveVariation negativeVariation
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ t ∈ Finset.range T,
        (max 0 (f (t + 1) - f t) - max 0 (f t - f (t + 1))) =
        ∑ t ∈ Finset.range T, (f (t + 1) - f t) := by
      apply Finset.sum_congr rfl
      intro t ht
      omega
    _ = f T - f 0 := Finset.sum_range_sub f T

/-- Potential variation is bounded from the actual initial/final sums;
the sum may oscillate arbitrarily between those endpoints. -/
theorem negativeVariation_le_positive (f : ℕ → ℤ) (T : ℕ) (N K : ℤ)
    (hstart : f 0 ≤ N * K) (hend : N ≤ f T) :
    negativeVariation f T ≤ N * (K - 1) + positiveVariation f T := by
  have h := variation_balance f T
  nlinarith

/-- Explicit arithmetic assembly after the geometric multiplicities
have supplied the component ledger inequalities. -/
theorem quantitative_collected (K N L P I Vp Vm E A : ℤ)
    (hK : 2 ≤ K)
    (hplus : Vp ≤ 4 * L * (K - 1) + P * K)
    (hminus : Vm ≤ N * (K - 1) + Vp)
    (hentries : E ≤ N + I + 2 * Vm + (2 * K + 4) * L)
    (hledger : A ≤ (5 * K - 1) * E + 6 * Vm +
      3 * (K + 1) * (Vp + Vm) + (2 * K + 4) * L) :
    A ≤ (13 * K^2 - K - 8) * N + (5 * K - 1) * I +
      (74 * K^2 - 4 * K - 40) * L + (16 * K^2 + 10 * K) * P := by
  have he := mul_le_mul_of_nonneg_left hentries (show 0 ≤ 5 * K - 1 by omega)
  have hm := mul_le_mul_of_nonneg_left hminus (show 0 ≤ 13 * K + 7 by omega)
  have hp := mul_le_mul_of_nonneg_left hplus (show 0 ≤ 16 * K + 10 by omega)
  nlinarith

theorem quantitative_quadratic (K N L P I Vp Vm E A : ℤ)
    (hK : 2 ≤ K) (hN : 0 ≤ N) (hL : 0 ≤ L) (hP : 0 ≤ P) (hI : 0 ≤ I)
    (hplus : Vp ≤ 4 * L * (K - 1) + P * K)
    (hminus : Vm ≤ N * (K - 1) + Vp)
    (hentries : E ≤ N + I + 2 * Vm + (2 * K + 4) * L)
    (hledger : A ≤ (5 * K - 1) * E + 6 * Vm +
      3 * (K + 1) * (Vp + Vm) + (2 * K + 4) * L) :
    A ≤ 74 * (N + I + L + P) * K^2 := by
  have h := quantitative_collected K N L P I Vp Vm E A hK hplus hminus hentries hledger
  have hn := mul_nonneg hN (show 0 ≤ 61 * K^2 + K + 8 by nlinarith)
  have hi := mul_nonneg hI (show 0 ≤ 74 * K^2 - 5 * K + 1 by nlinarith)
  have hl := mul_nonneg hL (show 0 ≤ 4 * K + 40 by omega)
  have hp := mul_nonneg hP (show 0 ≤ 58 * K^2 - 10 * K by nlinarith)
  nlinarith

end GreedyForest
