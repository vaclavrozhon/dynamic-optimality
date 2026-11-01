import ComparatorAtoms
import ExpansionRotations

/-!
Concrete plateau gap/separator partition, including null records, and the
two recursive lifting cases for canonical locality. The cut map is derived
from actual typed gap BSTs, not supplied as an abstract ordered partition.
-/
namespace GreedyMerge.PlateauBridge
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.OrderedAtoms
open GreedyMerge.ComparatorAtoms
open GreedyMerge.ExpansionRotations
open GreedyMerge.PortCases

def Cut (start : ℕ) (separator : ℕ → ℕ) (atom : ℕ) : ℕ :=
  if atom % 2 = 0 then 2 * GapLower start separator (atom / 2)
  else 2 * separator (atom / 2) + 1

def AtomOwner (separator gapOwner : ℕ → ℕ) (atom : ℕ) : ℕ :=
  if atom % 2 = 0 then gapOwner (atom / 2) else 2 * separator (atom / 2) + 1

@[simp] theorem cut_even (start : ℕ) (separator : ℕ → ℕ) (i : ℕ) :
    Cut start separator (2 * i) = 2 * GapLower start separator i := by
  have hdiv : (2 * i) / 2 = i := by omega
  have hmod : (2 * i) % 2 = 0 := by omega
  simp [Cut, hdiv, hmod]

@[simp] theorem cut_odd (start : ℕ) (separator : ℕ → ℕ) (i : ℕ) :
    Cut start separator (2 * i + 1) = 2 * separator i + 1 := by
  have hdiv : (2 * i + 1) / 2 = i := by omega
  have hmod : (2 * i + 1) % 2 = 1 := by omega
  simp [Cut, hdiv, hmod]

@[simp] theorem owner_even (separator gapOwner : ℕ → ℕ) (i : ℕ) :
    AtomOwner separator gapOwner (2 * i) = gapOwner i := by
  have hdiv : (2 * i) / 2 = i := by omega
  have hmod : (2 * i) % 2 = 0 := by omega
  simp [AtomOwner, hdiv, hmod]

@[simp] theorem owner_odd (separator gapOwner : ℕ → ℕ) (i : ℕ) :
    AtomOwner separator gapOwner (2 * i + 1) = 2 * separator i + 1 := by
  have hdiv : (2 * i + 1) / 2 = i := by omega
  have hmod : (2 * i + 1) % 2 = 1 := by omega
  simp [AtomOwner, hdiv, hmod]

@[simp] theorem cut_zero (start : ℕ) (separator : ℕ → ℕ) :
    Cut start separator 0 = 2 * start := by
  simpa only [GapLower] using cut_even start separator 0

/-- Every atom is nonempty in the external-record order, even if its real
key gap is empty: the gap still contains one external null record. -/
theorem cut_strictMono (start : ℕ) (separator : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower start separator i) (separator i)) :
    StrictMono (Cut start separator) := by
  apply strictMono_nat_of_lt_succ
  intro atom
  have hcases : atom % 2 = 0 ∨ atom % 2 = 1 := by omega
  rcases hcases with heven | hodd
  · have heq : atom = 2 * (atom / 2) := by omega
    conv_lhs => rw [heq, cut_even]
    have hnext : atom + 1 = 2 * (atom / 2) + 1 := by omega
    rw [hnext, cut_odd]
    have h := (gaps (atom / 2)).lower_le_upper
    omega
  · have heq : atom = 2 * (atom / 2) + 1 := by omega
    conv_lhs => rw [heq, cut_odd]
    have hnext : atom + 1 = 2 * (atom / 2 + 1) := by omega
    rw [hnext, cut_even]
    simp only [GapLower]
    omega

theorem singleton_uniqueMin (rank : ℕ → ℕ) (key : ℕ) : UniqueMin rank key key key := by
  refine ⟨⟨by omega, by omega, ?_⟩, ?_⟩
  · intro other hl hu
    have heq : other = key := by omega
    simp [heq]
  · intro other hl hu hne
    omega

theorem gap_owners_are_atom_owners {rank separator gapOwner : ℕ → ℕ} {start n : ℕ}
    (gapMin : ∀ i, i ≤ n → UniqueMin rank (2 * GapLower start separator i)
      (2 * separator i) (gapOwner i)) :
    AtomOwners rank (Cut start separator) (AtomOwner separator gapOwner) (2 * n + 1) := by
  intro atom hatom
  have hcases : atom % 2 = 0 ∨ atom % 2 = 1 := by omega
  rcases hcases with heven | hodd
  · have heq : atom = 2 * (atom / 2) := by omega
    have hnext : atom + 1 = 2 * (atom / 2) + 1 := by omega
    unfold AtomOwners at *
    rw [heq, owner_even, cut_even]
    rw [show 2 * (atom / 2) + 1 = 2 * (atom / 2) + 1 from rfl, cut_odd]
    have hsub : 2 * separator (atom / 2) + 1 - 1 = 2 * separator (atom / 2) := by omega
    rw [hsub]
    exact gapMin (atom / 2) (by omega)
  · have heq : atom = 2 * (atom / 2) + 1 := by omega
    have hnext : atom + 1 = 2 * (atom / 2 + 1) := by omega
    rw [hnext, heq, owner_odd, cut_odd, cut_even]
    simp only [GapLower]
    have hdiv : (2 * (atom / 2) + 1) / 2 = atom / 2 := by omega
    rw [hdiv]
    have hsub : 2 * (separator (atom / 2) + 1) - 1 = 2 * separator (atom / 2) + 1 := by omega
    rw [hsub]
    exact singleton_uniqueMin rank _

theorem locate_key_in_gap {start key i : ℕ} (separator : ℕ → ℕ)
    (gaps : ∀ j, BST (GapLower start separator j) (separator j))
    (hl : GapLower start separator i ≤ key) (hu : key < separator i) :
    locate (Cut start separator) (cut_strictMono start separator gaps) (2 * key + 1) = 2 * i := by
  apply locate_of_inside
  · rw [cut_even]
    omega
  · rw [cut_odd]
    omega

/-- Local canonical shape changes lift to the complete plateau with all
original gap trees restored, at exactly the same number of rotations. -/
theorem plateau_rotation_with_fixed_gaps
    {treeLo treeHi a b depth n start : ℕ} {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (separator gapOwner gapOwner' : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower start separator i) (separator i))
    (hl : treeLo ≤ start) (hu : separator n ≤ treeHi)
    (gapMin : ∀ i, i ≤ n → UniqueMin before.externalDepth
      (2 * GapLower start separator i) (2 * separator i) (gapOwner i))
    (gapMin' : ∀ i, i ≤ n → UniqueMin after.externalDepth
      (2 * GapLower start separator i) (2 * separator i) (gapOwner' i))
    (first second : BST 0 n)
    (hf : Canonical (fun atom => before.externalDepth (AtomOwner separator gapOwner atom)) first)
    (hs : Canonical (fun atom => after.externalDepth (AtomOwner separator gapOwner' atom)) second) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps
      (Expand start separator gaps first) (Expand start separator gaps second) := by
  obtain ⟨steps, hsteps, hrot⟩ := comparator_projection_rotations step
    (Cut start separator) (AtomOwner separator gapOwner) (AtomOwner separator gapOwner')
    (cut_strictMono start separator gaps)
    (by rw [cut_zero]; omega) (by rw [cut_odd]; omega)
    (gap_owners_are_atom_owners gapMin) (gap_owners_are_atom_owners gapMin')
    first second hf hs
  exact ⟨steps, hsteps, expand_steps start separator gaps hrot⟩

/-- The other hierarchy-induction case: both comparator keys lie in one
lower gap. The separator skeleton is provably identical, and changes in
that single recursive gap lift through it without additional rotations. -/
theorem plateau_one_changed_gap
    {treeLo treeHi a b depth n start key count : ℕ} {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (separator gapOwner gapOwner' : ℕ → ℕ)
    (gaps gaps' : ∀ i, BST (GapLower start separator i) (separator i))
    (hl : treeLo ≤ start) (hu : separator n ≤ treeHi) (hkey : key ≤ n)
    (hal : GapLower start separator key ≤ a) (hau : a < separator key)
    (hbl : GapLower start separator key ≤ b) (hbu : b < separator key)
    (gapMin : ∀ i, i ≤ n → UniqueMin before.externalDepth
      (2 * GapLower start separator i) (2 * separator i) (gapOwner i))
    (gapMin' : ∀ i, i ≤ n → UniqueMin after.externalDepth
      (2 * GapLower start separator i) (2 * separator i) (gapOwner' i))
    (first second : BST 0 n)
    (hf : Canonical (fun atom => before.externalDepth (AtomOwner separator gapOwner atom)) first)
    (hs : Canonical (fun atom => after.externalDepth (AtomOwner separator gapOwner' atom)) second)
    (heq : ∀ i, i ≤ n → i ≠ key → gaps i = gaps' i)
    (hrot : RotationSteps count (gaps key) (gaps' key)) :
    RotationSteps count (Expand start separator gaps first) (Expand start separator gaps' second) := by
  have hskeleton : first = second := comparator_same_atom_projection step
    (Cut start separator) (AtomOwner separator gapOwner) (AtomOwner separator gapOwner')
    (cut_strictMono start separator gaps)
    (by rw [cut_zero]; omega) (by rw [cut_odd]; omega)
    (gap_owners_are_atom_owners gapMin) (gap_owners_are_atom_owners gapMin')
    (by rw [locate_key_in_gap separator gaps hal hau, locate_key_in_gap separator gaps hbl hbu])
    first second hf hs
  subst second
  exact expand_one_gap start separator gaps gaps' first (by omega) hkey
    (fun i _ hi hne => heq i hi hne) hrot

end GreedyMerge.PlateauBridge

#print axioms GreedyMerge.PlateauBridge.plateau_rotation_with_fixed_gaps
#print axioms GreedyMerge.PlateauBridge.plateau_one_changed_gap
