import SurfaceOwners

/-!
Neighborhood and owner preservation inside fixed gap intervals. Heights may
increase arbitrarily outside the gap. If the old adjacent boundaries dominate
its internal heights, strict neighborhoods of all gap keys stay exactly the
same. With comparator-depth ranks, their unique owners therefore stay fixed.
-/

namespace GreedyMerge.Surface

open Splay.Tree
open Splay.Tree.BST

theorem segment_union {center left right key blocker : ℕ}
    (hkeyLo : min left right ≤ key) (hkeyHi : key ≤ max left right)
    (hblockLo : min center key ≤ blocker) (hblockHi : blocker ≤ max center key) :
    (min center left ≤ blocker ∧ blocker ≤ max center left) ∨
      (min center right ≤ blocker ∧ blocker ≤ max center right) := by
  omega

theorem neighborhood_between (height : ℕ → ℤ) {n center left right key : ℕ}
    (hleft : Neighborhood height n center left)
    (hright : Neighborhood height n center right)
    (hkeyLo : min left right ≤ key) (hkeyHi : key ≤ max left right) :
    Neighborhood height n center key := by
  have hlN := hleft.2.1
  have hrN := hright.2.1
  refine ⟨hleft.1, by omega, ?_⟩
  intro blocker hblockLo hblockHi hne
  rcases segment_union hkeyLo hkeyHi hblockLo hblockHi with h | h
  · exact hleft.2.2 blocker h.1 h.2 hne
  · exact hright.2.2 blocker h.1 h.2 hne

def IntervalUnique (rank : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ lo hi, lo ≤ hi → hi < n → ∃! key, IsIntervalMin rank lo hi key

theorem comparator_intervalUnique {n : ℕ} (comparator : BST 0 n) :
    IntervalUnique comparator.depth n := by
  intro lo hi hne hhi
  exact comparator.existsUnique_intervalDepthMin (Nat.zero_le lo) hne hhi

theorem owners_eq_of_neighborhood_eq {n center : ℕ}
    (before after : ℕ → ℤ) (rank oldOwner newOwner : ℕ → ℕ)
    (unique : IntervalUnique rank n)
    (oldOwners : Owners before rank oldOwner n)
    (newOwners : Owners after rank newOwner n) (hcenter : center < n)
    (same : ∀ key, Neighborhood before n center key ↔ Neighborhood after n center key) :
    oldOwner center = newOwner center := by
  obtain ⟨holdVisible, holdMin⟩ := oldOwners center hcenter
  obtain ⟨hnewVisible, hnewMin⟩ := newOwners center hcenter
  have hnewOld := (same (newOwner center)).2 hnewVisible
  let lo := min (oldOwner center) (newOwner center)
  let hi := max (oldOwner center) (newOwner center)
  have hne : lo ≤ hi := by dsimp [lo, hi]; omega
  have hhi : hi < n := by
    have h0 := holdVisible.2.1
    have h1 := hnewVisible.2.1
    dsimp [hi]
    omega
  have hall : ∀ key, lo ≤ key → key ≤ hi → Neighborhood before n center key := by
    intro key hklo hkhi
    exact neighborhood_between before holdVisible hnewOld hklo hkhi
  have hold : IsIntervalMin rank lo hi (oldOwner center) := by
    refine ⟨Nat.min_le_left _ _, Nat.le_max_left _ _, ?_⟩
    intro key hklo hkhi
    exact holdMin key (hall key hklo hkhi)
  have hnew : IsIntervalMin rank lo hi (newOwner center) := by
    refine ⟨Nat.min_le_right _ _, Nat.le_max_right _ _, ?_⟩
    intro key hklo hkhi
    exact hnewMin key ((same key).1 (hall key hklo hkhi))
  obtain ⟨minimum, hminimum, hunique⟩ := unique lo hi hne hhi
  exact (hunique _ hold).trans (hunique _ hnew).symm

theorem neighborhood_transfer_inside {n lo hi center key : ℕ}
    (before after : ℕ → ℤ)
    (same : ∀ z, lo ≤ z → z < hi → before z = after z)
    (hcenterLo : lo ≤ center) (hcenterHi : center < hi)
    (hkeyLo : lo ≤ key) (hkeyHi : key < hi)
    (visible : Neighborhood before n center key) :
    Neighborhood after n center key := by
  refine ⟨visible.1, visible.2.1, ?_⟩
  intro blocker hblockLo hblockHi hne
  have hbLo : lo ≤ blocker := by omega
  have hbHi : blocker < hi := by omega
  rw [← same blocker hbLo hbHi, ← same center hcenterLo hcenterHi]
  exact visible.2.2 blocker hblockLo hblockHi hne

/-- Raising outside heights cannot alter a gap's neighborhoods when its
old boundaries already dominate the internal center's height. -/
theorem neighborhood_preserved_in_gap {n lo hi center key : ℕ}
    (before after : ℕ → ℤ) (hhi : hi ≤ n)
    (same : ∀ z, lo ≤ z → z < hi → before z = after z)
    (increases : ∀ z, z < n → before z ≤ after z)
    (hcenterLo : lo ≤ center) (hcenterHi : center < hi)
    (lowerBarrier : lo = 0 ∨ before center ≤ before (lo - 1))
    (upperBarrier : hi = n ∨ before center ≤ before hi) :
    Neighborhood before n center key ↔ Neighborhood after n center key := by
  have newLower : lo = 0 ∨ after center ≤ after (lo - 1) := by
    rcases lowerBarrier with h | h
    · exact Or.inl h
    · right
      have hb := increases (lo - 1) (by omega)
      rw [← same center hcenterLo hcenterHi]
      omega
  have newUpper : hi = n ∨ after center ≤ after hi := by
    rcases upperBarrier with h | h
    · exact Or.inl h
    · by_cases hedge : hi = n
      · exact Or.inl hedge
      · right
        have hb := increases hi (by omega)
        rw [← same center hcenterLo hcenterHi]
        omega
  constructor
  · intro visible
    have inside := neighborhood_inside_barriers before hcenterLo hcenterHi hhi
      visible lowerBarrier upperBarrier
    exact neighborhood_transfer_inside before after same hcenterLo hcenterHi
      inside.1 inside.2 visible
  · intro visible
    have inside := neighborhood_inside_barriers after hcenterLo hcenterHi hhi
      visible newLower newUpper
    exact neighborhood_transfer_inside after before (fun z hzlo hzhi => (same z hzlo hzhi).symm)
      hcenterLo hcenterHi inside.1 inside.2 visible

theorem owner_preserved_in_gap {n lo hi center : ℕ}
    (before after : ℕ → ℤ) (rank oldOwner newOwner : ℕ → ℕ)
    (unique : IntervalUnique rank n)
    (oldOwners : Owners before rank oldOwner n)
    (newOwners : Owners after rank newOwner n) (hhi : hi ≤ n)
    (same : ∀ z, lo ≤ z → z < hi → before z = after z)
    (increases : ∀ z, z < n → before z ≤ after z)
    (hcenterLo : lo ≤ center) (hcenterHi : center < hi)
    (lowerBarrier : lo = 0 ∨ before center ≤ before (lo - 1))
    (upperBarrier : hi = n ∨ before center ≤ before hi) :
    oldOwner center = newOwner center := by
  apply owners_eq_of_neighborhood_eq before after rank oldOwner newOwner
    unique oldOwners newOwners (by omega)
  intro key
  exact neighborhood_preserved_in_gap before after hhi same increases
    hcenterLo hcenterHi lowerBarrier upperBarrier

end GreedyMerge.Surface

#print axioms GreedyMerge.Surface.owner_preserved_in_gap
