import MultiSplay.ComparatorSuffixReference
import ChaCha.Paper20261030.DepthPreferences
import Mathlib.Data.Finset.Card

/-!
# Persistent genuine bits and the single structural boundary departure

A suffix component reads genuine bits from their original depth intervals.
Intervals crossing its start are structural and point left. A depth access
can turn at most one such interval right: every changed interval separates
the same two depths, `start - 1` and the requested depth. Restoring these
structural bits therefore does not initialize or overwrite genuine memory.
-/

namespace MultiSplay.ComparatorSuffix

open ChaCha
open ChaCha.Paper20261030.Secondary (intervalUpdate)

def boundaryChanges {a b : Nat} (reference : DepthTree a b) (start request : Nat) :
    Finset DepthSplit := reference.nodes.filter fun split =>
      split.lo < start ∧ start ≤ split.cut ∧ split.cut < request ∧ request ≤ split.hi

theorem boundaryChanges_subsingleton {a b : Nat} (reference : DepthTree a b)
    (start request : Nat) :
    ∀ first ∈ boundaryChanges reference start request,
      ∀ second ∈ boundaryChanges reference start request, first = second := by
  intro first firstMember second secondMember
  obtain ⟨firstPresent, firstBounds⟩ := Finset.mem_filter.mp firstMember
  obtain ⟨secondPresent, secondBounds⟩ := Finset.mem_filter.mp secondMember
  have firstSeparates : first.Separates (start - 1) request := by
    unfold DepthSplit.Separates
    omega
  have secondSeparates : second.Separates (start - 1) request := by
    unfold DepthSplit.Separates
    omega
  have one := reference.locate_of_separates firstPresent firstSeparates
  have two := reference.locate_of_separates secondPresent secondSeparates
  exact Option.some.inj (one.symm.trans two)

theorem boundaryChanges_card {a b : Nat} (reference : DepthTree a b) (start request : Nat) :
    (boundaryChanges reference start request).card ≤ 1 :=
  Finset.card_le_one.mpr (boundaryChanges_subsingleton reference start request)

/-- Read a clipped record through its unchanged separator key. Boundary
records have a structural left preference, independent of genuine memory. -/
def preference {a b : Nat} (reference : DepthTree a b) (start : Nat)
    (memory : DepthSplit → Bool) (split : DepthSplit) : Bool :=
  match reference.locate split.cut (split.cut + 1) with
  | none => false
  | some original => if original.lo < start then false else memory original

/-- The logical memory operation writes only genuine original intervals. -/
def writeGenuine (start request : Nat) (memory : DepthSplit → Bool) : DepthSplit → Bool :=
  fun split => if start ≤ split.lo then intervalUpdate request memory split else memory split

def restoreBoundary {a b : Nat} (reference : DepthTree a b) (start : Nat)
    (bits : DepthSplit → Bool) (split : DepthSplit) : Bool :=
  match reference.locate split.cut (split.cut + 1) with
  | none => false
  | some original => if original.lo < start then false else bits split

theorem preference_genuine {a b : Nat} (reference : DepthTree a b) (start : Nat)
    (memory : DepthSplit → Bool) {split : DepthSplit}
    (member : split ∈ reference.nodes) (genuine : start ≤ split.lo) :
    preference reference start memory split = memory split := by
  simp only [preference, original_of_cut reference member, if_neg (by omega : ¬split.lo < start)]

theorem writeGenuine_structural (start request : Nat) (memory : DepthSplit → Bool)
    {split : DepthSplit} (structural : split.lo < start) :
    writeGenuine start request memory split = memory split := by
  simp only [writeGenuine, if_neg (by omega : ¬ start ≤ split.lo)]

/-- Access followed by structural restoration reads exactly the updated
persistent genuine memory at every actual node of the induced reference. -/
theorem restore_access_eq {a b : Nat} (reference : DepthTree a b)
    (start : Nat) (lower : a ≤ start) (upper : start ≤ b)
    (request : Nat) (memory : DepthSplit → Bool) {split : DepthSplit}
    (member : split ∈ (suffix reference start lower upper).nodes) :
    restoreBoundary reference start (intervalUpdate request (preference reference start memory)) split =
      preference reference start (writeGenuine start request memory) split := by
  obtain ⟨original, present, lookup, same⟩ := suffix_original_lookup reference start lower upper member
  by_cases structural : original.lo < start
  · simp only [restoreBoundary, preference, lookup, if_pos structural]
  · have genuine : start ≤ original.lo := by omega
    have equal : split = original := same.symm.trans (clip_genuine start original genuine)
    rw [equal] at lookup ⊢
    simp only [restoreBoundary, preference, lookup, if_neg structural, writeGenuine,
      if_pos genuine, intervalUpdate]

/-- Every structural bit changed by a real induced-reference access belongs
to the concrete singleton-or-empty boundary set above. -/
theorem changed_boundary_mem {a b : Nat} (reference : DepthTree a b)
    (start request : Nat) (memory : DepthSplit → Bool) {original : DepthSplit}
    (member : original ∈ reference.nodes) (retained : start ≤ original.cut)
    (structural : original.lo < start)
    (changed : intervalUpdate request (preference reference start memory) (clip start original) ≠
      preference reference start memory (clip start original)) :
    original ∈ boundaryChanges reference start request := by
  have lookup : reference.locate (clip start original).cut ((clip start original).cut + 1) = some original :=
    original_of_cut reference member
  have old : preference reference start memory (clip start original) = false := by
    simp only [preference, lookup, if_pos structural]
  rw [old] at changed
  simp only [intervalUpdate] at changed
  have bounds : (clip start original).lo ≤ request ∧ request ≤ (clip start original).hi := by
    by_contra outside
    exact changed (by simp only [if_neg outside, old])
  rw [if_pos bounds] at changed
  have right : original.cut < request := by
    by_contra notRight
    exact changed (decide_eq_false notRight)
  exact Finset.mem_filter.mpr ⟨member, structural, retained, right, bounds.2⟩

end MultiSplay.ComparatorSuffix
