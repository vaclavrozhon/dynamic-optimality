import SurfaceOwners

/-!
The fixed-left-tie canonical height/priority refinement. The key priorities
may be the ranks of strict-neighborhood owners. Existence, uniqueness, and
dependence only on priorities inside the interval are proved here.
-/

namespace GreedyMerge.Surface

open Splay.Tree
open Splay.Tree.BST

def Canonical (height : ℕ → ℤ) (priority : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ key, lo ≤ key → key < hi → height key ≤ height root) ∧
      (∀ key, lo ≤ key → key < hi → height key = height root →
        priority root ≤ priority key) ∧
      (∀ key, lo ≤ key → key < hi → height key = height root →
        priority key = priority root → root ≤ key) ∧
      Canonical height priority left ∧ Canonical height priority right

theorem canonical_refines {lo hi : ℕ} (height : ℕ → ℤ) (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (h : Canonical height (fun key => rank (owner key)) tree) :
    Refines height rank owner tree := by
  induction tree with
  | empty => trivial
  | node left right ihLeft ihRight =>
      exact ⟨h.1, h.2.1, ihLeft h.2.2.2.1, ihRight h.2.2.2.2⟩

theorem canonical_unique {lo hi : ℕ} (height : ℕ → ℤ) (priority : ℕ → ℕ)
    (first second : BST lo hi)
    (hfirst : Canonical height priority first)
    (hsecond : Canonical height priority second) : first = second := by
  induction first with
  | empty i =>
      cases second with
      | empty => rfl
      | node left right =>
          have hlo := left.lower_le_upper
          have hhi := right.lower_le_upper
          omega
  | @node lo root hi left right ihLeft ihRight =>
      cases second with
      | empty =>
          have hlo := left.lower_le_upper
          have hhi := right.lower_le_upper
          omega
      | @node lo other hi otherLeft otherRight =>
          have hlo := left.lower_le_upper
          have hhi := right.lower_le_upper
          have holo := otherLeft.lower_le_upper
          have hohi := otherRight.lower_le_upper
          have hheight12 := hfirst.1 other holo (by omega)
          have hheight21 := hsecond.1 root hlo (by omega)
          have hheight : height other = height root := by omega
          have hp12 := hfirst.2.1 other holo (by omega) hheight
          have hp21 := hsecond.2.1 root hlo (by omega) hheight.symm
          have hpriority : priority other = priority root := by omega
          have hk12 := hfirst.2.2.1 other holo (by omega) hheight hpriority
          have hk21 := hsecond.2.2.1 root hlo (by omega) hheight.symm hpriority.symm
          have heq : other = root := by omega
          subst other
          have hleft := ihLeft otherLeft hfirst.2.2.2.1 hsecond.2.2.2.1
          have hright := ihRight otherRight hfirst.2.2.2.2 hsecond.2.2.2.2
          cases hleft
          cases hright
          rfl

theorem exists_canonical (height : ℕ → ℤ) (priority : ℕ → ℕ)
    (lo hi : ℕ) (horder : lo ≤ hi) :
    ∃ tree : BST lo hi, Canonical height priority tree := by
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
        obtain ⟨best, hbestMem, hbestMin⟩ :=
          Finset.exists_min_image maxima priority hmaxima
        let bests := maxima.filter fun key => priority key = priority best
        have hbests : bests.Nonempty := by
          exact ⟨best, Finset.mem_filter.mpr ⟨hbestMem, rfl⟩⟩
        obtain ⟨root, hrootMem, hrootLeft⟩ :=
          Finset.exists_min_image bests (fun key => key) hbests
        have hrootMaxima := (Finset.mem_filter.mp hrootMem).1
        have hrootIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hrootMaxima).1
        have hheight : height root = height top := (Finset.mem_filter.mp hrootMaxima).2
        have hpriority : priority root = priority best := (Finset.mem_filter.mp hrootMem).2
        obtain ⟨left, hleft⟩ := ih (root - lo) (by omega) lo root hrootIco.1 rfl
        obtain ⟨right, hright⟩ := ih (hi - (root + 1)) (by omega)
          (root + 1) hi (by omega) rfl
        refine ⟨.node left right, ?_, ?_, ?_, hleft, hright⟩
        · intro key hklo hkhi
          rw [hheight]
          exact htopMax key (Finset.mem_Ico.mpr ⟨hklo, hkhi⟩)
        · intro key hklo hkhi hkeyHeight
          rw [hpriority]
          apply hbestMin key
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hklo, hkhi⟩,
            hkeyHeight.trans hheight⟩
        · intro key hklo hkhi hkeyHeight hkeyPriority
          apply hrootLeft key
          apply Finset.mem_filter.mpr
          refine ⟨?_, hkeyPriority.trans hpriority⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hklo, hkhi⟩,
            hkeyHeight.trans hheight⟩

theorem canonical_congr_on {lo hi : ℕ}
    (before after : ℕ → ℤ) (oldPriority newPriority : ℕ → ℕ)
    (tree : BST lo hi)
    (sameHeight : ∀ key, lo ≤ key → key < hi → before key = after key)
    (samePriority : ∀ key, lo ≤ key → key < hi → oldPriority key = newPriority key)
    (canonical : Canonical before oldPriority tree) :
    Canonical after newPriority tree := by
  induction tree with
  | empty => trivial
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have hrootHeight := sameHeight root hlo (by omega)
      have hrootPriority := samePriority root hlo (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro key hklo hkhi
        rw [← sameHeight key hklo hkhi, ← hrootHeight]
        exact canonical.1 key hklo hkhi
      · intro key hklo hkhi hheight
        rw [← sameHeight key hklo hkhi, ← hrootHeight] at hheight
        rw [← samePriority key hklo hkhi, ← hrootPriority]
        exact canonical.2.1 key hklo hkhi hheight
      · intro key hklo hkhi hheight hpriority
        rw [← sameHeight key hklo hkhi, ← hrootHeight] at hheight
        rw [← samePriority key hklo hkhi, ← hrootPriority] at hpriority
        exact canonical.2.2.1 key hklo hkhi hheight hpriority
      · apply ihLeft
        · exact fun key hklo hkhi => sameHeight key hklo (by omega)
        · exact fun key hklo hkhi => samePriority key hklo (by omega)
        · exact canonical.2.2.2.1
      · apply ihRight
        · exact fun key hklo hkhi => sameHeight key (by omega) hkhi
        · exact fun key hklo hkhi => samePriority key (by omega) hkhi
        · exact canonical.2.2.2.2

theorem canonical_eq_of_priorities_eq {lo hi : ℕ}
    (before after : ℕ → ℤ) (oldPriority newPriority : ℕ → ℕ)
    (oldTree newTree : BST lo hi)
    (sameHeight : ∀ key, lo ≤ key → key < hi → before key = after key)
    (samePriority : ∀ key, lo ≤ key → key < hi → oldPriority key = newPriority key)
    (oldCanonical : Canonical before oldPriority oldTree)
    (newCanonical : Canonical after newPriority newTree) : oldTree = newTree := by
  exact canonical_unique after newPriority oldTree newTree
    (canonical_congr_on before after oldPriority newPriority oldTree
      sameHeight samePriority oldCanonical) newCanonical

end GreedyMerge.Surface

#print axioms GreedyMerge.Surface.canonical_unique
#print axioms GreedyMerge.Surface.exists_canonical
