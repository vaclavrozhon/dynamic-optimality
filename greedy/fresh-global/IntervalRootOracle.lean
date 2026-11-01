import Splay.Tree.DepthMin

/-!
A fixed-tie interval-root oracle for the canonical plateau refinement.
Atoms have zero-based indices: even 2*i is gap g_i and odd 2*i+1 is
separator q_i. Separator ranges are half-open [lo,hi), and expand to the
closed atom interval [2*lo,2*hi].

This file does NOT assume that root positions are invariant under a rank
change. It proves that property from preservation of expanded-interval
minimum positions, including the repeated priorities caused by gap minima.
-/
namespace GreedyMerge.IntervalRootOracle
open Splay.Tree
open Splay.Tree.BST

def Priority (rank : ℕ → ℕ) (separator : ℕ) : ℕ :=
  min (rank (2 * separator))
    (min (rank (2 * separator + 1)) (rank (2 * separator + 2)))

def UniqueMin (rank : ℕ → ℕ) (lo hi owner : ℕ) : Prop :=
  IsIntervalMin rank lo hi owner ∧
    ∀ other, lo ≤ other → other ≤ hi → other ≠ owner → rank owner < rank other

/-- The leftmost separator adjacent to `owner` inside this separator range. -/
def leftPort (lo owner : ℕ) : ℕ := max lo ((owner - 1) / 2)

def LeftmostRoot (priority : ℕ → ℕ) (lo hi root : ℕ) : Prop :=
  lo ≤ root ∧ root < hi ∧
    (∀ key, lo ≤ key → key < hi → priority root ≤ priority key) ∧
    (∀ key, lo ≤ key → key < root → priority root < priority key)

theorem leftPort_bounds {lo hi owner : ℕ}
    (hne : lo < hi) (hl : 2 * lo ≤ owner) (hu : owner ≤ 2 * hi) :
    lo ≤ leftPort lo owner ∧ leftPort lo owner < hi ∧
      2 * leftPort lo owner ≤ owner ∧ owner ≤ 2 * leftPort lo owner + 2 := by
  unfold leftPort
  by_cases h : lo ≤ (owner - 1) / 2
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left (by omega : (owner - 1) / 2 ≤ lo)]
    omega

theorem atom_right_of_earlier_separator {lo owner key : ℕ}
    (hlo : lo ≤ key) (hearlier : key < leftPort lo owner) :
    2 * key + 2 < owner := by
  unfold leftPort at hearlier
  by_cases h : lo ≤ (owner - 1) / 2
  · rw [max_eq_right h] at hearlier
    omega
  · rw [max_eq_left (by omega : (owner - 1) / 2 ≤ lo)] at hearlier
    omega

theorem priority_le_atom (rank : ℕ → ℕ) {separator atom : ℕ}
    (hl : 2 * separator ≤ atom) (hu : atom ≤ 2 * separator + 2) :
    Priority rank separator ≤ rank atom := by
  have hcases : atom = 2 * separator ∨ atom = 2 * separator + 1 ∨
      atom = 2 * separator + 2 := by omega
  rcases hcases with h | h | h
  · rw [h]
    exact Nat.min_le_left _ _
  · rw [h]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  · rw [h]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

theorem full_min_le_priority {rank : ℕ → ℕ} {lo hi owner key : ℕ}
    (hmin : IsIntervalMin rank (2 * lo) (2 * hi) owner)
    (hl : lo ≤ key) (hu : key < hi) :
    rank owner ≤ Priority rank key := by
  unfold Priority
  apply Nat.le_min.mpr
  constructor
  · exact hmin.2.2 _ (by omega) (by omega)
  · apply Nat.le_min.mpr
    constructor
    · exact hmin.2.2 _ (by omega) (by omega)
    · exact hmin.2.2 _ (by omega) (by omega)

/-- An atom minimum determines the minimum priority at its selected port. -/
theorem leftPort_priority {rank : ℕ → ℕ} {lo hi owner : ℕ}
    (hne : lo < hi) (hmin : IsIntervalMin rank (2 * lo) (2 * hi) owner) :
    Priority rank (leftPort lo owner) = rank owner := by
  obtain ⟨hl, hu, hcoverl, hcoveru⟩ :=
    leftPort_bounds hne hmin.1 hmin.2.1
  exact Nat.le_antisymm (priority_le_atom rank hcoverl hcoveru)
    (full_min_le_priority hmin hl hu)

/-- The minimum atom identifies the root even when two adjacent separator
priorities are equal. Leftmost tie-breaking is part of the conclusion. -/
theorem leftPort_is_leftmost_root {rank : ℕ → ℕ} {lo hi owner : ℕ}
    (hne : lo < hi) (hmin : UniqueMin rank (2 * lo) (2 * hi) owner) :
    LeftmostRoot (Priority rank) lo hi (leftPort lo owner) := by
  obtain ⟨hl, hu, _, _⟩ := leftPort_bounds hne hmin.1.1 hmin.1.2.1
  refine ⟨hl, hu, ?_, ?_⟩
  · intro key hklo hkhi
    rw [leftPort_priority hne hmin.1]
    exact full_min_le_priority hmin.1 hklo hkhi
  · intro key hklo hkroot
    have hatom := atom_right_of_earlier_separator hklo hkroot
    rw [leftPort_priority hne hmin.1]
    unfold Priority
    apply Nat.lt_min.mpr
    constructor
    · exact hmin.2 _ (by omega) (by omega) (by omega)
    · apply Nat.lt_min.mpr
      constructor
      · exact hmin.2 _ (by omega) (by omega) (by omega)
      · exact hmin.2 _ (by omega) (by omega) (by omega)

theorem leftmost_root_unique {priority : ℕ → ℕ} {lo hi first second : ℕ}
    (hf : LeftmostRoot priority lo hi first)
    (hs : LeftmostRoot priority lo hi second) : first = second := by
  by_cases h : first < second
  · have hlt := hs.2.2.2 first hf.1 h
    have hle := hf.2.2.1 second hs.1 hs.2.1
    omega
  · by_cases h' : second < first
    · have hlt := hf.2.2.2 second hs.1 h'
      have hle := hs.2.2.1 first hf.1 hf.2.1
      omega
    · omega

def Canonical (rank : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      LeftmostRoot (Priority rank) lo hi root ∧
        Canonical rank left ∧ Canonical rank right

/-- Agreement is about positions of interval minima, not numeric priorities.
It can therefore hold when many ranks change, or when a gap's representative
changes identity but remains the minimum at the same atom position. -/
def SameMinPositions (rank rank' : ℕ → ℕ) (start finish : ℕ) : Prop :=
  ∀ lo hi, start ≤ lo → lo < hi → hi ≤ finish →
    ∃ owner, UniqueMin rank (2 * lo) (2 * hi) owner ∧
      UniqueMin rank' (2 * lo) (2 * hi) owner

theorem sameMinPositions_mono {rank rank' : ℕ → ℕ} {start finish lo hi : ℕ}
    (h : SameMinPositions rank rank' start finish)
    (hl : start ≤ lo) (hu : hi ≤ finish) : SameMinPositions rank rank' lo hi := by
  intro a b ha hab hb
  exact h a b (by omega) hab (by omega)

/-- Equal minimum-atom positions on expanded separator intervals imply
identical entire fixed-tie canonical BSTs, including all recursive roots. -/
theorem canonical_eq_of_sameMinPositions {rank rank' : ℕ → ℕ} {lo hi : ℕ}
    (first second : BST lo hi) (hf : Canonical rank first)
    (hs : Canonical rank' second) (hpositions : SameMinPositions rank rank' lo hi) :
    first = second := by
  induction first with
  | empty boundary =>
      cases second with
      | empty => rfl
      | node left right =>
          have := left.lower_le_upper
          have := right.lower_le_upper
          omega
  | @node lo root hi left right ihLeft ihRight =>
      cases second with
      | empty =>
          have := left.lower_le_upper
          have := right.lower_le_upper
          omega
      | @node _ root' _ left' right' =>
          have hrootlo := left.lower_le_upper
          have hroothi := right.lower_le_upper
          obtain ⟨hfroot, hfl, hfr⟩ := hf
          obtain ⟨hsroot, hsl, hsr⟩ := hs
          obtain ⟨owner, hmin, hmin'⟩ := hpositions lo hi (by omega)
            (by omega) (by omega)
          have hr : root = leftPort lo owner := leftmost_root_unique hfroot
            (leftPort_is_leftmost_root (by omega) hmin)
          have hr' : root' = leftPort lo owner := leftmost_root_unique hsroot
            (leftPort_is_leftmost_root (by omega) hmin')
          have hroots : root' = root := by omega
          clear hr hr'
          subst root'
          have heql : left = left' := ihLeft left' hfl hsl
            (sameMinPositions_mono hpositions (by omega) (by omega))
          have heqr : right = right' := ihRight right' hfr hsr
            (sameMinPositions_mono hpositions (by omega) (by omega))
          cases heql
          cases heqr
          rfl

/-- Fixed-tie canonical existence follows constructively from the oracle:
no numerical ordering of unrelated ranks or arbitrary tie choices is used. -/
theorem exists_canonical (rank : ℕ → ℕ) (lo hi : ℕ) (h : lo ≤ hi)
    (hminima : SameMinPositions rank rank lo hi) :
    ∃ tree : BST lo hi, Canonical rank tree := by
  generalize hsize : hi - lo = size
  induction size using Nat.strong_induction_on generalizing lo hi with
  | h size ih =>
      by_cases heq : lo = hi
      · subst hi
        exact ⟨.empty lo, trivial⟩
      · have hlt : lo < hi := by omega
        obtain ⟨owner, hmin, _⟩ := hminima lo hi (by omega) hlt (by omega)
        have hroot := leftPort_is_leftmost_root hlt hmin
        have hrootlo := hroot.1
        have hroothi := hroot.2.1
        obtain ⟨left, hleft⟩ := ih (leftPort lo owner - lo) (by omega)
          lo (leftPort lo owner) hrootlo
          (sameMinPositions_mono hminima (by omega) (by omega)) rfl
        obtain ⟨right, hright⟩ := ih (hi - (leftPort lo owner + 1)) (by omega)
          (leftPort lo owner + 1) hi (by omega)
          (sameMinPositions_mono hminima (by omega) (by omega)) rfl
        exact ⟨.node left right, hroot, hleft, hright⟩

end GreedyMerge.IntervalRootOracle

#print axioms GreedyMerge.IntervalRootOracle.leftPort_is_leftmost_root
#print axioms GreedyMerge.IntervalRootOracle.canonical_eq_of_sameMinPositions

#print axioms GreedyMerge.IntervalRootOracle.exists_canonical
