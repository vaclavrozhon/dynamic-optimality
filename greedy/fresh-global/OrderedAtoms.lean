import SharpProjection
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic

/-!
Ordered contraction of consecutive nonempty record intervals into atoms.
The atom minimum position is derived from the original interval minimum,
not assumed to be stable under rank changes. Empty real-key gaps can still
be nonempty record intervals because they contain their null record.
-/
namespace GreedyMerge.OrderedAtoms
open Splay.Tree
open GreedyMerge.IntervalRootOracle
open GreedyMerge.ProjectionRotation
open GreedyMerge.SharpProjection
open GreedyMerge.PortCases

/-- Fixed cut positions partition the record order into nonempty atoms. -/
def AtomOwners (rank cut owner : ℕ → ℕ) (count : ℕ) : Prop :=
  ∀ atom, atom < count → UniqueMin rank (cut atom) (cut (atom + 1) - 1) (owner atom)

theorem index_le_cut (cut : ℕ → ℕ) (hcut : StrictMono cut) (index : ℕ) :
    index ≤ cut index := by
  induction index with
  | zero => omega
  | succ i ih =>
      have h := hcut (by omega : i < i + 1)
      omega

theorem exists_cut_above (cut : ℕ → ℕ) (hcut : StrictMono cut) (key : ℕ) :
    ∃ atom, key < cut (atom + 1) := by
  exact ⟨key, by have h := index_le_cut cut hcut (key + 1); omega⟩

noncomputable def locate (cut : ℕ → ℕ) (hcut : StrictMono cut) (key : ℕ) : ℕ :=
  Nat.find (exists_cut_above cut hcut key)

theorem locate_bounds (cut : ℕ → ℕ) (hcut : StrictMono cut) {key : ℕ}
    (hkey : cut 0 ≤ key) :
    cut (locate cut hcut key) ≤ key ∧ key < cut (locate cut hcut key + 1) := by
  have hu := Nat.find_spec (exists_cut_above cut hcut key)
  change key < cut (locate cut hcut key + 1) at hu
  refine ⟨?_, hu⟩
  by_cases hz : locate cut hcut key = 0
  · simpa [hz] using hkey
  · have hm := Nat.find_min (exists_cut_above cut hcut key)
      (by omega : locate cut hcut key - 1 < locate cut hcut key)
    have heq : locate cut hcut key - 1 + 1 = locate cut hcut key := by omega
    rw [heq] at hm
    omega

theorem locate_range (cut : ℕ → ℕ) (hcut : StrictMono cut) {lo hi key : ℕ}
    (hl : cut lo ≤ key) (hu : key < cut (hi + 1)) :
    lo ≤ locate cut hcut key ∧ locate cut hcut key ≤ hi := by
  have hzero := hcut.monotone (by omega : 0 ≤ lo)
  obtain ⟨hkl, hku⟩ := locate_bounds cut hcut (by omega : cut 0 ≤ key)
  constructor
  · by_contra h
    have hmono := hcut.monotone (by omega : locate cut hcut key + 1 ≤ lo)
    omega
  · by_contra h
    have hmono := hcut.monotone (by omega : hi + 1 ≤ locate cut hcut key)
    omega

theorem locate_of_inside (cut : ℕ → ℕ) (hcut : StrictMono cut) {atom key : ℕ}
    (hl : cut atom ≤ key) (hu : key < cut (atom + 1)) :
    locate cut hcut key = atom := by
  have h := locate_range cut hcut hl hu
  omega

theorem owner_inside_range {rank cut owner : ℕ → ℕ} {count lo hi atom : ℕ}
    (hcut : StrictMono cut) (owners : AtomOwners rank cut owner count)
    (hlo : lo ≤ atom) (hhi : atom ≤ hi) (hcount : hi < count) :
    cut lo ≤ owner atom ∧ owner atom < cut (hi + 1) := by
  have hm := owners atom (by omega)
  have hml := hm.1.1
  have hmu := hm.1.2.1
  have hl := hcut.monotone hlo
  have hu := hcut.monotone (by omega : atom + 1 ≤ hi + 1)
  have hpos := hcut (by omega : 0 < atom + 1)
  omega

/-- Contracting atoms sends an actual interval minimum to its containing
atom, with full uniqueness. Numeric atom priorities are true owner ranks. -/
theorem contract_min {rank cut owner : ℕ → ℕ} {count lo hi key : ℕ}
    (hcut : StrictMono cut) (owners : AtomOwners rank cut owner count)
    (horder : lo ≤ hi) (hcount : hi < count)
    (hmin : UniqueMin rank (cut lo) (cut (hi + 1) - 1) key) :
    UniqueMin (fun atom => rank (owner atom)) lo hi (locate cut hcut key) := by
  have hpos := hcut (by omega : 0 < hi + 1)
  have hkeyl := hmin.1.1
  have hkeyu : key < cut (hi + 1) := by have h := hmin.1.2.1; omega
  have hloc := locate_range cut hcut hkeyl hkeyu
  have hzero := hcut.monotone (by omega : 0 ≤ lo)
  have hlocbounds := locate_bounds cut hcut (by omega : cut 0 ≤ key)
  have howner := owners (locate cut hcut key) (by omega)
  have hownerRange := owner_inside_range hcut owners hloc.1 hloc.2 hcount
  have hsame : owner (locate cut hcut key) = key := by
    by_contra hne
    have hlt := hmin.2 (owner (locate cut hcut key)) hownerRange.1
      (by omega) hne
    have hle := howner.1.2.2 key hlocbounds.1 (by omega)
    omega
  refine ⟨⟨hloc.1, hloc.2, ?_⟩, ?_⟩
  · intro atom hal hau
    have hinside := owner_inside_range hcut owners hal hau hcount
    dsimp only
    rw [hsame]
    exact hmin.1.2.2 (owner atom) hinside.1 (by omega)
  · intro atom hal hau hne
    have hm := owners atom (by omega)
    have hinside := owner_inside_range hcut owners hal hau hcount
    have hownerNe : owner atom ≠ key := by
      intro heq
      have hlocal := owner_inside_range hcut owners (lo := atom) (hi := atom)
        (Nat.le_refl atom) (Nat.le_refl atom) (by omega)
      have hlocated := locate_of_inside cut hcut hm.1.1 hlocal.2
      rw [heq] at hlocated
      exact hne hlocated.symm
    dsimp only
    rw [hsame]
    exact hmin.2 (owner atom) hinside.1 (by omega) hownerNe

/-- Directed changes for arbitrary closed record intervals. -/
def RecordChanges (rank rank' : ℕ → ℕ) (start finish a b : ℕ) : Prop :=
  ∀ lo hi, start ≤ lo → lo ≤ hi → hi ≤ finish →
    ∃ old new, UniqueMin rank lo hi old ∧ UniqueMin rank' lo hi new ∧
      (old = new ∨ old = a ∧ new = b)

/-- A concrete ordered contraction preserves directed interval-minimum
changes. The atom identities of a and b are fixed by the cut positions. -/
theorem changes_contract {rank rank' cut owner owner' : ℕ → ℕ} {n a b : ℕ}
    (hcut : StrictMono cut)
    (owners : AtomOwners rank cut owner (2 * n + 1))
    (owners' : AtomOwners rank' cut owner' (2 * n + 1))
    (hchange : RecordChanges rank rank' (cut 0) (cut (2 * n + 1) - 1) a b) :
    ChangesOnly (fun atom => rank (owner atom)) (fun atom => rank' (owner' atom))
      0 n (locate cut hcut a) (locate cut hcut b) := by
  intro lo hi _ hnonempty hhi
  have hl := hcut.monotone (by omega : 0 ≤ 2 * lo)
  have hu := hcut.monotone (by omega : 2 * hi + 1 ≤ 2 * n + 1)
  have hstrict := hcut (by omega : 2 * lo < 2 * hi + 1)
  obtain ⟨old, new, ho, hn, hs⟩ := hchange (cut (2 * lo)) (cut (2 * hi + 1) - 1)
    hl (by omega) (by omega)
  refine ⟨locate cut hcut old, locate cut hcut new,
    contract_min hcut owners (by omega) (by omega) ho,
    contract_min hcut owners' (by omega) (by omega) hn, ?_⟩
  rcases hs with heq | ⟨ha, hb⟩
  · exact Or.inl (congrArg (locate cut hcut) heq)
  · exact Or.inr ⟨congrArg (locate cut hcut) ha, congrArg (locate cut hcut) hb⟩

/-- The full separator projection changes by at most two rotations after
ordered atom contraction; no quotient-tree rotation is assumed. -/
theorem contracted_projection_rotations
    {rank rank' cut owner owner' : ℕ → ℕ} {n a b : ℕ}
    (hcut : StrictMono cut)
    (owners : AtomOwners rank cut owner (2 * n + 1))
    (owners' : AtomOwners rank' cut owner' (2 * n + 1))
    (hchange : RecordChanges rank rank' (cut 0) (cut (2 * n + 1) - 1) a b)
    (first second : BST 0 n)
    (hf : Canonical (fun atom => rank (owner atom)) first)
    (hs : Canonical (fun atom => rank' (owner' atom)) second) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps first second :=
  projection_rotations first second hf hs (changes_contract hcut owners owners' hchange)

/-- If both changed record identities are in one atom, its representative
may change but the complete separator projection stays identical. -/
theorem same_atom_projection_eq
    {rank rank' cut owner owner' : ℕ → ℕ} {n a b : ℕ}
    (hcut : StrictMono cut)
    (owners : AtomOwners rank cut owner (2 * n + 1))
    (owners' : AtomOwners rank' cut owner' (2 * n + 1))
    (hchange : RecordChanges rank rank' (cut 0) (cut (2 * n + 1) - 1) a b)
    (hsame : locate cut hcut a = locate cut hcut b)
    (first second : BST 0 n)
    (hf : Canonical (fun atom => rank (owner atom)) first)
    (hs : Canonical (fun atom => rank' (owner' atom)) second) : first = second := by
  apply canonical_eq_of_sameMinPositions first second hf hs
  intro lo hi hlow hnonempty hhigh
  obtain ⟨old, new, ho, hn, hc⟩ :=
    changes_contract hcut owners owners' hchange lo hi hlow hnonempty hhigh
  have heq : old = new := by rcases hc with heq | ⟨ha, hb⟩ <;> omega
  subst new
  exact ⟨old, ho, hn⟩

end GreedyMerge.OrderedAtoms

#print axioms GreedyMerge.OrderedAtoms.changes_contract
#print axioms GreedyMerge.OrderedAtoms.contracted_projection_rotations
#print axioms GreedyMerge.OrderedAtoms.same_atom_projection_eq
