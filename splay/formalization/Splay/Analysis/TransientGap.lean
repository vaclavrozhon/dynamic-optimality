import Splay.Analysis.ContractedGap
import Mathlib.Data.Finset.Basic

namespace Splay.Analysis

/--
Point gap in a transient lazy-interval state.

Raw heap gaps may temporarily be negative while a junction and its rank update
are performed non-atomically. Subtracting the signed interval minimum first
produces the nonnegative quantity consumed by `contractedGap`.
-/
def transientPointGap (rawGap intervalGap : ℤ) : ℕ :=
  (rawGap - intervalGap).toNat

/-- Contracted point gap associated with a possibly signed raw heap gap. -/
def transientContractedGap (rawGap intervalGap : ℤ) : ℕ :=
  contractedGap (transientPointGap rawGap intervalGap)

/--
An integer is the interval gap precisely when it is attained by a member and
is a lower bound for every member's raw gap.
-/
def IsIntervalGap {α : Type*} [DecidableEq α]
    (members : Finset α) (rawGap : α → ℤ) (intervalGap : ℤ) : Prop :=
  (∃ member ∈ members, rawGap member = intervalGap) ∧
    ∀ member ∈ members, intervalGap ≤ rawGap member

/-- Subtracting a genuine interval minimum yields the intended signed value. -/
theorem transientPointGap_coe_eq {rawGap intervalGap : ℤ}
    (hMin : intervalGap ≤ rawGap) :
    (transientPointGap rawGap intervalGap : ℤ) =
      rawGap - intervalGap := by
  unfold transientPointGap
  rw [Int.toNat_of_nonneg]
  omega

/-- A uniform signed shift of both components leaves the point gap unchanged. -/
@[simp]
theorem transientPointGap_add_shift
    (rawGap intervalGap shift : ℤ) :
    transientPointGap (rawGap + shift) (intervalGap + shift) =
      transientPointGap rawGap intervalGap := by
  unfold transientPointGap
  have hDifference :
      rawGap + shift - (intervalGap + shift) =
        rawGap - intervalGap := by
    omega
  rw [hDifference]

/-- A uniform signed shift therefore also preserves the contracted point gap. -/
@[simp]
theorem transientContractedGap_add_shift
    (rawGap intervalGap shift : ℤ) :
    transientContractedGap (rawGap + shift) (intervalGap + shift) =
      transientContractedGap rawGap intervalGap := by
  simp [transientContractedGap]

/-- Raising a nonnegative interval gap can only decrease the point gap. -/
theorem transientPointGap_le_zeroGap
    {rawGap intervalGap : ℤ}
    (intervalNonnegative : 0 ≤ intervalGap)
    (intervalLeRaw : intervalGap ≤ rawGap) :
    transientPointGap rawGap intervalGap ≤
      transientPointGap rawGap 0 := by
  have rawNonnegative : 0 ≤ rawGap := intervalNonnegative.trans intervalLeRaw
  have shiftedCoe := transientPointGap_coe_eq intervalLeRaw
  have zeroCoe := transientPointGap_coe_eq rawNonnegative
  apply Int.ofNat_le.mp
  rw [shiftedCoe, zeroCoe]
  omega

/-- The corresponding contracted value is likewise nonincreasing. -/
theorem transientContractedGap_le_zeroGap
    {rawGap intervalGap : ℤ}
    (intervalNonnegative : 0 ≤ intervalGap)
    (intervalLeRaw : intervalGap ≤ rawGap) :
    transientContractedGap rawGap intervalGap ≤
      transientContractedGap rawGap 0 := by
  exact contractedGap_mono
    (transientPointGap_le_zeroGap intervalNonnegative intervalLeRaw)

/-- Raising an attained interval gap can only decrease a member's point gap. -/
theorem transientPointGap_antitone_intervalGap
    {rawGap oldGap newGap : ℤ}
    (oldLeNew : oldGap ≤ newGap) (newLeRaw : newGap ≤ rawGap) :
    transientPointGap rawGap newGap ≤
      transientPointGap rawGap oldGap := by
  have oldLeRaw : oldGap ≤ rawGap := oldLeNew.trans newLeRaw
  have newCoe := transientPointGap_coe_eq newLeRaw
  have oldCoe := transientPointGap_coe_eq oldLeRaw
  apply Int.ofNat_le.mp
  rw [newCoe, oldCoe]
  omega

/-- Contracting preserves antitonicity in the interval gap. -/
theorem transientContractedGap_antitone_intervalGap
    {rawGap oldGap newGap : ℤ}
    (oldLeNew : oldGap ≤ newGap) (newLeRaw : newGap ≤ rawGap) :
    transientContractedGap rawGap newGap ≤
      transientContractedGap rawGap oldGap := by
  exact contractedGap_mono
    (transientPointGap_antitone_intervalGap oldLeNew newLeRaw)

/-- Every member has a well-defined nonnegative point gap. -/
theorem IsIntervalGap.interval_le {α : Type*} [DecidableEq α]
    {members : Finset α} {rawGap : α → ℤ} {intervalGap : ℤ}
    (hInterval : IsIntervalGap members rawGap intervalGap)
    {member : α} (hMember : member ∈ members) :
    intervalGap ≤ rawGap member :=
  hInterval.2 member hMember

/-- The minimum over a set is no larger than the minimum over a nonempty
subset.  This is the numerical reason that splitting can only decrease point
gaps. -/
theorem IsIntervalGap.le_of_subset {α : Type*} [DecidableEq α]
    {members subset : Finset α} {rawGap : α → ℤ}
    {memberGap subsetGap : ℤ}
    (memberMinimum : IsIntervalGap members rawGap memberGap)
    (subsetMinimum : IsIntervalGap subset rawGap subsetGap)
    (included : subset ⊆ members) :
    memberGap ≤ subsetGap := by
  obtain ⟨minimizer, minimizerMember, attains⟩ := subsetMinimum.1
  rw [← attains]
  exact memberMinimum.2 minimizer (included minimizerMember)

/-- An attained finite interval minimum is unique. -/
theorem IsIntervalGap.unique {α : Type*} [DecidableEq α]
    {members : Finset α} {rawGap : α → ℤ} {first second : ℤ}
    (firstMinimum : IsIntervalGap members rawGap first)
    (secondMinimum : IsIntervalGap members rawGap second) :
    first = second := by
  obtain ⟨firstMember, firstInside, firstAttains⟩ := firstMinimum.1
  obtain ⟨secondMember, secondInside, secondAttains⟩ := secondMinimum.1
  have secondLeFirst := secondMinimum.2 firstMember firstInside
  have firstLeSecond := firstMinimum.2 secondMember secondInside
  rw [firstAttains] at secondLeFirst
  rw [secondAttains] at firstLeSecond
  omega

/-- Uniformly shifting all raw gaps also shifts their attained minimum. -/
theorem IsIntervalGap.add_shift {α : Type*} [DecidableEq α]
    {members : Finset α} {rawGap : α → ℤ} {intervalGap : ℤ}
    (hInterval : IsIntervalGap members rawGap intervalGap) (shift : ℤ) :
    IsIntervalGap members (fun member => rawGap member + shift)
      (intervalGap + shift) := by
  obtain ⟨minimizer, hMinimizer, hAttains⟩ := hInterval.1
  have hLower := hInterval.2
  refine ⟨⟨minimizer, hMinimizer, ?_⟩, ?_⟩
  · simp only
    rw [hAttains]
  intro member hMember
  change intervalGap + shift ≤ rawGap member + shift
  have hMemberLower := hLower member hMember
  omega

@[simp]
theorem transientPointGap_self (rawGap : ℤ) :
    transientPointGap rawGap rawGap = 0 := by
  simp [transientPointGap]

@[simp]
theorem transientContractedGap_self (rawGap : ℤ) :
    transientContractedGap rawGap rawGap = 1 := by
  simp [transientContractedGap, contractedGap, gapBucket]

/--
Every attained interval minimum has point gap zero and contracted point gap
one, regardless of whether the common raw gap is positive or negative.
-/
theorem IsIntervalGap.minimizer_gaps {α : Type*} [DecidableEq α]
    {members : Finset α} {rawGap : α → ℤ} {intervalGap : ℤ}
    (hInterval : IsIntervalGap members rawGap intervalGap) :
    ∃ member ∈ members,
      transientPointGap (rawGap member) intervalGap = 0 ∧
        transientContractedGap (rawGap member) intervalGap = 1 := by
  obtain ⟨member, hMember, hRawGap⟩ := hInterval.1
  refine ⟨member, hMember, ?_, ?_⟩
  · rw [hRawGap]
    exact transientPointGap_self intervalGap
  · rw [hRawGap]
    exact transientContractedGap_self intervalGap

/--
A singleton shrinking interval therefore has contracted point gap one even
when its raw gap is temporarily negative.
-/
theorem singleton_transientContractedGap
    {α : Type*} [DecidableEq α] (member : α) (rawGap : α → ℤ) :
    transientContractedGap (rawGap member) (rawGap member) = 1 :=
  transientContractedGap_self _

end Splay.Analysis
