import Splay.Tree.DepthMin
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Filter

/-!
Direct surface-height characterization of exact owners. A refinement first
maximizes height, then minimizes neighborhood-owner rank among equal-height
keys. This is the same local priority order used by plateau refinement.
The main theorem below derives subtree minima from actual strict-height
neighborhoods, rather than assuming a neighborhood/plateau identification.
-/

namespace GreedyMerge.Surface

open Splay.Tree
open Splay.Tree.BST

def Neighborhood (height : ℕ → ℤ) (n center key : ℕ) : Prop :=
  center < n ∧ key < n ∧
    ∀ blocker, min center key ≤ blocker → blocker ≤ max center key →
      blocker ≠ center → height blocker < height center

def Owners (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ center, center < n → Neighborhood height n center (owner center) ∧
    ∀ key, Neighborhood height n center key → rank (owner center) ≤ rank key

def Distance (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

theorem neighborhood_self (height : ℕ → ℤ) {n center : ℕ} (h : center < n) :
    Neighborhood height n center center := by
  refine ⟨h, h, ?_⟩
  intro blocker hl hu hne
  simp only [Nat.min_self, Nat.max_self] at hl hu
  omega

theorem distance_strict_between {a b c : ℕ}
    (hl : min a b ≤ c) (hu : c ≤ max a b) (hne : c ≠ a) :
    Distance c b < Distance a b := by
  by_cases hab : a ≤ b
  · have hcb : c ≤ b := by simpa [Nat.max_eq_right hab] using hu
    have hac : a ≤ c := by simpa [Nat.min_eq_left hab] using hl
    simp only [Distance, if_pos hab, if_pos hcb]
    omega
  · have hba : b ≤ a := by omega
    have hbc : b ≤ c := by simpa [Nat.min_eq_right hba] using hl
    have hca : c ≤ a := by simpa [Nat.max_eq_left hba] using hu
    by_cases hcb : c ≤ b
    · simp only [Distance, if_neg hab, if_pos hcb]
      omega
    · simp only [Distance, if_neg hab, if_neg hcb]
      omega

/-- Every key in a range is visible from some maximum-height separator
of that range. Pick the nearest maximum to the key. -/
theorem covered_by_maximum {n lo hi root key : ℕ}
    (height : ℕ → ℤ) (hhi : hi ≤ n)
    (hrootLo : lo ≤ root) (hrootHi : root < hi)
    (hkeyLo : lo ≤ key) (hkeyHi : key < hi)
    (hmax : ∀ z, lo ≤ z → z < hi → height z ≤ height root) :
    ∃ separator, lo ≤ separator ∧ separator < hi ∧
      height separator = height root ∧ Neighborhood height n separator key := by
  classical
  let maxima := (Finset.Ico lo hi).filter fun z => height z = height root
  have hnonempty : maxima.Nonempty := by
    refine ⟨root, ?_⟩
    simp [maxima, hrootLo, hrootHi]
  obtain ⟨separator, hsepMem, hnear⟩ :=
    Finset.exists_min_image maxima (fun z => Distance z key) hnonempty
  have hsep : lo ≤ separator ∧ separator < hi ∧ height separator = height root := by
    simpa only [maxima, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hsepMem
  refine ⟨separator, hsep.1, hsep.2.1, hsep.2.2, ?_⟩
  refine ⟨by omega, by omega, ?_⟩
  intro blocker hblockLo hblockHi hne
  have hbLo : lo ≤ blocker := by
    have hm : lo ≤ min separator key := Nat.le_min.mpr ⟨hsep.1, hkeyLo⟩
    omega
  have hbHi : blocker < hi := by
    have hm : max separator key < hi := Nat.max_lt.mpr ⟨hsep.2.1, hkeyHi⟩
    omega
  have hheight := hmax blocker hbLo hbHi
  have hneq : height blocker ≠ height root := by
    intro heq
    have hmem : blocker ∈ maxima := by simp [maxima, hbLo, hbHi, heq]
    have hdist := hnear blocker hmem
    have hstrict := distance_strict_between hblockLo hblockHi hne
    omega
  rw [hsep.2.2]
  omega

def Refines (height : ℕ → ℤ) (rank owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ key, lo ≤ key → key < hi → height key ≤ height root) ∧
      (∀ key, lo ≤ key → key < hi → height key = height root →
        rank (owner root) ≤ rank (owner key)) ∧
      Refines height rank owner left ∧ Refines height rank owner right

def ExactOwners (rank owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      IsIntervalMin rank lo (hi - 1) (owner root) ∧
        ExactOwners rank owner left ∧ ExactOwners rank owner right

theorem neighborhood_inside_barriers {n lo hi center key : ℕ}
    (height : ℕ → ℤ) (hcenterLo : lo ≤ center) (hcenterHi : center < hi)
    (_hhi : hi ≤ n) (hneighborhood : Neighborhood height n center key)
    (lowerBarrier : lo = 0 ∨ height center ≤ height (lo - 1))
    (upperBarrier : hi = n ∨ height center ≤ height hi) :
    lo ≤ key ∧ key < hi := by
  obtain ⟨hc, hk, hvisible⟩ := hneighborhood
  constructor
  · by_contra h
    have hklo : key < lo := by omega
    rcases lowerBarrier with hzero | hheight
    · omega
    · have hl : min center key ≤ lo - 1 := by
        have hm := Nat.min_le_right center key
        omega
      have hu : lo - 1 ≤ max center key := by
        have hm := Nat.le_max_left center key
        omega
      have hlt := hvisible (lo - 1) hl hu (by omega)
      omega
  · by_contra h
    have hikey : hi ≤ key := by omega
    rcases upperBarrier with heq | hheight
    · omega
    · have hl : min center key ≤ hi := by
        have hm := Nat.min_le_left center key
        omega
      have hu : hi ≤ max center key := by
        have hm := Nat.le_max_right center key
        omega
      have hlt := hvisible hi hl hu (by omega)
      omega

/-- Surface priority refinement implies the actual strict-neighborhood
owner is the minimum-rank key of each subtree. -/
theorem refines_exactOwners {n lo hi : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (owners : Owners height rank owner n) (hhi : hi ≤ n)
    (refines : Refines height rank owner tree)
    (lowerBarrier : lo = 0 ∨ ∀ key, lo ≤ key → key < hi →
      height key ≤ height (lo - 1))
    (upperBarrier : hi = n ∨ ∀ key, lo ≤ key → key < hi →
      height key ≤ height hi) :
    ExactOwners rank owner tree := by
  induction tree with
  | empty => trivial
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hmax, hpriority, hrefLeft, hrefRight⟩ := refines
      have hlo := left.lower_le_upper
      have hrootHi := right.lower_le_upper
      have hrootN : root < n := by omega
      obtain ⟨hownerVisible, hownerMin⟩ := owners root hrootN
      have hbarLo : lo = 0 ∨ height root ≤ height (lo - 1) := by
        rcases lowerBarrier with h | h
        · exact Or.inl h
        · exact Or.inr (h root hlo (by omega))
      have hbarHi : hi = n ∨ height root ≤ height hi := by
        rcases upperBarrier with h | h
        · exact Or.inl h
        · exact Or.inr (h root hlo (by omega))
      have hownerInside := neighborhood_inside_barriers height hlo (by omega)
        hhi hownerVisible hbarLo hbarHi
      have hwhole : IsIntervalMin rank lo (hi - 1) (owner root) := by
        refine ⟨hownerInside.1, by omega, ?_⟩
        intro key hklo hkhi
        have hkeyHi : key < hi := by omega
        obtain ⟨separator, hslo, hshi, hheight, hvisible⟩ :=
          covered_by_maximum height hhi hlo (by omega) hklo hkeyHi hmax
        have hsepOwner := (owners separator (by omega)).2 key hvisible
        exact Nat.le_trans (hpriority separator hslo hshi hheight) hsepOwner
      have lowerLeft : lo = 0 ∨ ∀ key, lo ≤ key → key < root →
          height key ≤ height (lo - 1) := by
        rcases lowerBarrier with h | h
        · exact Or.inl h
        · exact Or.inr (fun key hklo hkhi => h key hklo (by omega))
      have upperLeft : root = n ∨ ∀ key, lo ≤ key → key < root →
          height key ≤ height root := by
        exact Or.inr (fun key hklo hkhi => hmax key hklo (by omega))
      have lowerRight : root + 1 = 0 ∨ ∀ key, root + 1 ≤ key → key < hi →
          height key ≤ height ((root + 1) - 1) := by
        right
        intro key hklo hkhi
        simpa using hmax key (by omega) hkhi
      have upperRight : hi = n ∨ ∀ key, root + 1 ≤ key → key < hi →
          height key ≤ height hi := by
        rcases upperBarrier with h | h
        · exact Or.inl h
        · exact Or.inr (fun key hklo hkhi => h key (by omega) hkhi)
      exact ⟨hwhole, ihLeft (by omega) hrefLeft lowerLeft upperLeft,
        ihRight hhi hrefRight lowerRight upperRight⟩

theorem full_refinement_exactOwners {n : ℕ}
    (height : ℕ → ℤ) (rank owner : ℕ → ℕ) (tree : BST 0 n)
    (owners : Owners height rank owner n) (refines : Refines height rank owner tree) :
    ExactOwners rank owner tree := by
  exact refines_exactOwners height rank owner tree owners (Nat.le_refl n) refines
    (Or.inl rfl) (Or.inl rfl)

theorem exists_neighborhood_owner (height : ℕ → ℤ) (rank : ℕ → ℕ)
    {n center : ℕ} (hcenter : center < n) :
    ∃ owner, Neighborhood height n center owner ∧
      ∀ key, Neighborhood height n center key → rank owner ≤ rank key := by
  classical
  let candidates := (Finset.range n).filter (Neighborhood height n center)
  have hnonempty : candidates.Nonempty := by
    exact ⟨center, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hcenter, neighborhood_self height hcenter⟩⟩
  obtain ⟨owner, howner, hmin⟩ := Finset.exists_min_image candidates rank hnonempty
  refine ⟨owner, (Finset.mem_filter.mp howner).2, ?_⟩
  intro key hkey
  exact hmin key (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkey.2.1, hkey⟩)

theorem exists_owners (height : ℕ → ℤ) (rank : ℕ → ℕ) (n : ℕ) :
    ∃ owner, Owners height rank owner n := by
  classical
  let owner := fun center => if h : center < n then
      Classical.choose (exists_neighborhood_owner height rank h) else center
  refine ⟨owner, ?_⟩
  intro center hcenter
  dsimp only [owner]
  rw [dif_pos hcenter]
  exact Classical.choose_spec (exists_neighborhood_owner height rank hcenter)

/-- Height-first, owner-rank-second refinements exist for every finite
surface. A fixed leftmost tie rule can be imposed separately. -/
theorem exists_refines (height : ℕ → ℤ) (rank owner : ℕ → ℕ)
    (lo hi : ℕ) (horder : lo ≤ hi) :
    ∃ tree : BST lo hi, Refines height rank owner tree := by
  classical
  generalize hsize : hi - lo = size
  induction size using Nat.strong_induction_on generalizing lo hi with
  | h size ih =>
      by_cases heq : lo = hi
      · subst hi
        exact ⟨.empty lo, trivial⟩
      · have hlt : lo < hi := by omega
        have hnonempty : (Finset.Ico lo hi).Nonempty := by
          exact ⟨lo, by simp [hlt]⟩
        obtain ⟨top, htopMem, htopMax⟩ :=
          Finset.exists_max_image (Finset.Ico lo hi) height hnonempty
        let maxima := (Finset.Ico lo hi).filter fun key => height key = height top
        have hmaxima : maxima.Nonempty := by
          exact ⟨top, Finset.mem_filter.mpr ⟨htopMem, rfl⟩⟩
        obtain ⟨root, hrootMem, hpriority⟩ :=
          Finset.exists_min_image maxima (fun key => rank (owner key)) hmaxima
        have hrootIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hrootMem).1
        have hheight : height root = height top := (Finset.mem_filter.mp hrootMem).2
        obtain ⟨left, hleft⟩ := ih (root - lo) (by omega) lo root hrootIco.1 rfl
        obtain ⟨right, hright⟩ := ih (hi - (root + 1)) (by omega)
          (root + 1) hi (by omega) rfl
        refine ⟨.node left right, ?_, ?_, hleft, hright⟩
        · intro key hklo hkhi
          rw [hheight]
          exact htopMax key (Finset.mem_Ico.mpr ⟨hklo, hkhi⟩)
        · intro key hklo hkhi hkeyHeight
          apply hpriority key
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hklo, hkhi⟩,
            hkeyHeight.trans hheight⟩

/-- The required owner-exact tree exists for every finite surface and rank
assignment. Unique comparator interval minima may subsequently identify the
owners canonically; no such uniqueness is needed for this existence claim. -/
theorem exists_owner_exact_refinement (height : ℕ → ℤ) (rank : ℕ → ℕ) (n : ℕ) :
    ∃ (owner : ℕ → ℕ) (tree : BST 0 n), Owners height rank owner n ∧
      Refines height rank owner tree ∧ ExactOwners rank owner tree := by
  obtain ⟨owner, howner⟩ := exists_owners height rank n
  obtain ⟨tree, htree⟩ := exists_refines height rank owner 0 n (Nat.zero_le n)
  exact ⟨owner, tree, howner, htree,
    full_refinement_exactOwners height rank owner tree howner htree⟩

end GreedyMerge.Surface

#print axioms GreedyMerge.Surface.full_refinement_exactOwners
#print axioms GreedyMerge.Surface.exists_owner_exact_refinement
