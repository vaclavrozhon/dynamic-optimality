import IntervalRootOracle
import PortRotationCases

/-!
Sharp projection locality from interval-minimum changes. The input interface
says that every changed expanded-interval minimum changes only a -> b.
The proof is about concrete canonical indexed BSTs and concrete rotations.
-/
namespace GreedyMerge.ProjectionRotation
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.PortCases

/-- The full atom-query interface of a single input rotation, restricted to
expanded separator intervals. Unchanged numerical ranks are not required. -/
def ChangesOnly (rank rank' : ℕ → ℕ) (start finish a b : ℕ) : Prop :=
  ∀ lo hi, start ≤ lo → lo < hi → hi ≤ finish →
    ∃ old new, UniqueMin rank (2 * lo) (2 * hi) old ∧
      UniqueMin rank' (2 * lo) (2 * hi) new ∧
      (old = new ∨ old = a ∧ new = b)

theorem ChangesOnly.mono {rank rank' : ℕ → ℕ} {start finish lo hi a b : ℕ}
    (h : ChangesOnly rank rank' start finish a b)
    (hl : start ≤ lo) (hu : hi ≤ finish) : ChangesOnly rank rank' lo hi a b := by
  intro l u hsl hlu huf
  exact h l u (by omega) hlu (by omega)

theorem ChangesOnly.symm {rank rank' : ℕ → ℕ} {start finish a b : ℕ}
    (h : ChangesOnly rank rank' start finish a b) :
    ChangesOnly rank' rank start finish b a := by
  intro l u hsl hlu huf
  obtain ⟨old, new, ho, hn, hs⟩ := h l u hsl hlu huf
  refine ⟨new, old, hn, ho, ?_⟩
  rcases hs with hs | ⟨ha, hb⟩
  · exact Or.inl hs.symm
  · exact Or.inr ⟨hb, ha⟩

theorem uniqueMin_unique {rank : ℕ → ℕ} {lo hi a b : ℕ}
    (ha : UniqueMin rank lo hi a) (hb : UniqueMin rank lo hi b) : a = b := by
  by_contra hne
  have hlt := ha.2 b hb.1.1 hb.1.2.1 (Ne.symm hne)
  have hle := hb.1.2.2 a ha.1.1 ha.1.2.1
  omega

theorem UniqueMin.restrict {rank : ℕ → ℕ} {lo hi l u owner : ℕ}
    (h : UniqueMin rank lo hi owner) (hl : lo ≤ l) (hu : u ≤ hi)
    (hol : l ≤ owner) (hou : owner ≤ u) : UniqueMin rank l u owner := by
  refine ⟨⟨hol, hou, ?_⟩, ?_⟩
  · intro key hkl hku
    exact h.1.2.2 key (by omega) (by omega)
  · intro key hkl hku hne
    exact h.2 key (by omega) (by omega) hne

theorem ChangesOnly.same_of_excludes {rank rank' : ℕ → ℕ} {lo hi a b : ℕ}
    (h : ChangesOnly rank rank' lo hi a b)
    (hexcludes : a < 2 * lo ∨ 2 * hi < a ∨ b < 2 * lo ∨ 2 * hi < b) :
    SameMinPositions rank rank' lo hi := by
  intro l u hll hlu huu
  obtain ⟨old, new, ho, hn, hs⟩ := h l u hll hlu huu
  rcases hs with hs | ⟨ha, hb⟩
  · subst new
    exact ⟨old, ho, hn⟩
  · have hal := ho.1.1
    have hau := ho.1.2.1
    have hbl := hn.1.1
    have hbu := hn.1.2.1
    rcases hexcludes with hx | hx | hx | hx <;> omega

theorem canonical_eq_of_excludes {rank rank' : ℕ → ℕ} {lo hi a b : ℕ}
    (first second : BST lo hi) (hf : Canonical rank first)
    (hs : Canonical rank' second) (h : ChangesOnly rank rank' lo hi a b)
    (hexcludes : a < 2 * lo ∨ 2 * hi < a ∨ b < 2 * lo ∨ 2 * hi < b) :
    first = second :=
  canonical_eq_of_sameMinPositions first second hf hs (h.same_of_excludes hexcludes)

theorem root_of_min {rank : ℕ → ℕ} {lo root hi owner : ℕ}
    {left : BST lo root} {right : BST (root + 1) hi}
    (hcan : Canonical rank (.node left right))
    (hmin : UniqueMin rank (2 * lo) (2 * hi) owner) :
    root = leftPort lo owner := by
  have hl := left.lower_le_upper
  have hu := right.lower_le_upper
  exact leftmost_root_unique hcan.1 (leftPort_is_leftmost_root (by omega) hmin)

theorem leftPort_raise_lower {lo next owner : ℕ}
    (hlo : lo ≤ next) (hroot : next ≤ leftPort lo owner) :
    leftPort next owner = leftPort lo owner := by
  unfold leftPort at *
  by_cases h : lo ≤ (owner - 1) / 2
  · rw [max_eq_right h] at hroot ⊢
    exact max_eq_right hroot
  · rw [max_eq_left (by omega : (owner - 1) / 2 ≤ lo)] at hroot ⊢
    have heq : next = lo := by omega
    rw [heq, max_eq_left (by omega : (owner - 1) / 2 ≤ lo)]

theorem min_stable_when_new_excluded {rank rank' : ℕ → ℕ} {lo hi a b : ℕ}
    (h : ChangesOnly rank rank' lo hi a b) (hne : lo < hi)
    (hmin : UniqueMin rank (2 * lo) (2 * hi) a)
    (hex : b < 2 * lo ∨ 2 * hi < b) :
    UniqueMin rank' (2 * lo) (2 * hi) a := by
  obtain ⟨old, new, ho, hn, hs⟩ := h lo hi (by omega) hne (by omega)
  have heq := uniqueMin_unique ho hmin
  subst old
  rcases hs with hs | ⟨_, hb⟩
  · subst new
    exact hn
  · have hbl := hn.1.1
    have hbu := hn.1.2.1
    rcases hex with hx | hx <;> omega

theorem leftPort_mono_owner {lo a b : ℕ} (h : a ≤ b) :
    leftPort lo a ≤ leftPort lo b := by
  unfold leftPort
  omega

theorem owner_above_nonleft_port {lo owner root : ℕ}
    (hr : root = leftPort lo owner) (hlo : lo < root) : 2 * root < owner := by
  have h := atom_right_of_earlier_separator (by omega : lo ≤ root - 1)
    (by omega : root - 1 < leftPort lo owner)
  omega

/-- The changed-root case consists of one or two rotations through a common
fringe, proved directly from the interval-minimum interface. -/
theorem changed_roots {rank rank' : ℕ → ℕ} {lo p q hi a b : ℕ}
    (A : BST lo p) (oldRight : BST (p + 1) hi)
    (newLeft : BST lo q) (D : BST (q + 1) hi)
    (hold : Canonical rank (.node A oldRight))
    (hnew : Canonical rank' (.node newLeft D))
    (hpq : p < q)
    (hchange : ChangesOnly rank rank' lo hi a b)
    (ha : UniqueMin rank (2 * lo) (2 * hi) a)
    (hb : UniqueMin rank' (2 * lo) (2 * hi) b) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps (.node A oldRight) (.node newLeft D) := by
  have hlp := A.lower_le_upper
  have hphi := oldRight.lower_le_upper
  have hlq := newLeft.lower_le_upper
  have hqhi := D.lower_le_upper
  have hpa := root_of_min hold ha
  have hqb := root_of_min hnew hb
  have hacover := leftPort_bounds (by omega : lo < hi) ha.1.1 ha.1.2.1
  have hbcover := leftPort_bounds (by omega : lo < hi) hb.1.1 hb.1.2.1
  have halower : 2 * p ≤ a := by omega
  have haupper : a ≤ 2 * p + 2 := by omega
  have hbq : 2 * q < b := owner_above_nonleft_port hqb (by omega)
  have hnewLeftMin : UniqueMin rank' (2 * lo) (2 * q) a :=
    min_stable_when_new_excluded (hchange.mono (by omega) (by omega))
      (by omega) (UniqueMin.restrict ha (by omega) (by omega) (by omega) (by omega))
      (Or.inr hbq)
  cases newLeft with
  | empty => omega
  | @node _ r _ A' midNew =>
      have hr : r = p := by
        have h := root_of_min hnew.2.1 hnewLeftMin
        omega
      subst r
      cases oldRight with
      | empty => omega
      | @node _ s _ midOld rightOld =>
          have hps := midOld.lower_le_upper
          have hshi := rightOld.lower_le_upper
          obtain ⟨old, new, ho, hn, hswitch⟩ :=
            hchange (p + 1) hi (by omega) (by omega) (by omega)
          have hnewb : new = b := uniqueMin_unique hn
            (UniqueMin.restrict hb (by omega) (by omega) (by omega) (by omega))
          subst new
          have hspos := root_of_min hold.2.2 ho
          have hs_cases : s = q ∨ (s = p + 1 ∧ a = 2 * (p + 1)) := by
            rcases hswitch with holdb | ⟨holda, _⟩
            · subst old
              left
              rw [leftPort_raise_lower (by omega : lo ≤ p + 1)
                (by omega : p + 1 ≤ leftPort lo b)] at hspos
              omega
            · subst old
              right
              have hoa := ho.1.1
              have hae : a = 2 * (p + 1) := by omega
              refine ⟨?_, hae⟩
              rw [hae] at hspos
              unfold leftPort at hspos
              omega
          clear hspos
          by_cases hsq : s = q
          · subst s
            have eqA : A = A' := canonical_eq_of_excludes A A'
              hold.2.1 hnew.2.1.2.1
              (hchange.mono (by omega) (by omega)) (Or.inr (Or.inr (Or.inr (by omega))))
            have eqM : midOld = midNew := canonical_eq_of_excludes midOld midNew
              hold.2.2.2.1 hnew.2.1.2.2
              (hchange.mono (by omega) (by omega)) (Or.inr (Or.inr (Or.inr (by omega))))
            have eqD : rightOld = D := canonical_eq_of_excludes rightOld D
              hold.2.2.2.2 hnew.2.2
              (hchange.mono (by omega) (by omega)) (Or.inl (by omega))
            cases eqA
            cases eqM
            cases eqD
            exact ⟨1, by omega, crossOnePort _ _ _⟩
          · have hs : s = p + 1 := (hs_cases.resolve_left hsq).1
            have has : a = 2 * (p + 1) := (hs_cases.resolve_left hsq).2
            have hsq' : s < q := by omega
            have hRightMin : UniqueMin rank (2 * (s + 1)) (2 * hi) b := by
              exact min_stable_when_new_excluded
                ((hchange.mono (by omega) (by omega)).symm)
                (by omega)
                (UniqueMin.restrict hb (by omega) (by omega) (by omega) (by omega))
                (Or.inl (by omega))
            cases rightOld with
            | empty => omega
            | @node _ t _ C oldD =>
                have ht : t = q := by
                  have h := root_of_min hold.2.2.2.2 hRightMin
                  rw [leftPort_raise_lower (by omega : lo ≤ s + 1)
                    (by omega : s + 1 ≤ leftPort lo b)] at h
                  omega
                subst t
                have hMidMin : UniqueMin rank' (2 * (p + 1)) (2 * q) a :=
                  min_stable_when_new_excluded
                    (hchange.mono (by omega) (by omega)) (by omega)
                    (UniqueMin.restrict ha (by omega) (by omega) (by omega) (by omega))
                    (Or.inr hbq)
                cases midNew with
                | empty => omega
                | @node _ u _ newB newC =>
                    have hu : u = s := by
                      have h := root_of_min hnew.2.1.2.2 hMidMin
                      rw [has] at h
                      unfold leftPort at h
                      omega
                    subst u
                    have eqA : A = A' := canonical_eq_of_excludes A A'
                      hold.2.1 hnew.2.1.2.1
                      (hchange.mono (by omega) (by omega))
                      (Or.inr (Or.inr (Or.inr (by omega))))
                    have eqB : midOld = newB := canonical_eq_of_excludes midOld newB
                      hold.2.2.2.1 hnew.2.1.2.2.2.1
                      (hchange.mono (by omega) (by omega))
                      (Or.inr (Or.inr (Or.inr (by omega))))
                    have eqC : C = newC := canonical_eq_of_excludes C newC
                      hold.2.2.2.2.2.1 hnew.2.1.2.2.2.2
                      (hchange.mono (by omega) (by omega))
                      (Or.inr (Or.inr (Or.inr (by omega))))
                    have eqD : oldD = D := canonical_eq_of_excludes oldD D
                      hold.2.2.2.2.2.2 hnew.2.2
                      (hchange.mono (by omega) (by omega)) (Or.inl (by omega))
                    cases eqA
                    cases eqB
                    cases eqC
                    cases eqD
                    exact ⟨2, by omega, crossTwoPorts _ _ _ _⟩

/-- The complete sharp locality theorem at the interval-oracle interface.
Every changed expanded-interval minimum is allowed to change only a -> b;
all other minima are preserved. No common fringe is assumed. -/
theorem projection_rotations {rank rank' : ℕ → ℕ} {lo hi a b : ℕ}
    (first second : BST lo hi) (hf : Canonical rank first)
    (hs : Canonical rank' second) (hchange : ChangesOnly rank rank' lo hi a b) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps first second := by
  induction first with
  | empty boundary =>
      cases second with
      | empty => exact ⟨0, by omega, .refl _⟩
      | node left right =>
          have := left.lower_le_upper
          have := right.lower_le_upper
          omega
  | @node lo p hi left right ihLeft ihRight =>
      have hlp := left.lower_le_upper
      have hphi := right.lower_le_upper
      cases second with
      | empty => omega
      | @node _ q _ left' right' =>
          have hlq := left'.lower_le_upper
          have hqhi := right'.lower_le_upper
          by_cases heq : q = p
          · subst q
            by_cases ha : a ≤ 2 * p
            · have heqr : right = right' := canonical_eq_of_excludes right right'
                hf.2.2 hs.2.2 (hchange.mono (by omega) (by omega)) (Or.inl (by omega))
              obtain ⟨steps, hsteps, hrot⟩ := ihLeft left' hf.2.1 hs.2.1
                (hchange.mono (by omega) (by omega))
              cases heqr
              exact ⟨steps, hsteps, hrot.leftContext _⟩
            · have heql : left = left' := canonical_eq_of_excludes left left'
                hf.2.1 hs.2.1 (hchange.mono (by omega) (by omega))
                (Or.inr (Or.inl (by omega)))
              obtain ⟨steps, hsteps, hrot⟩ := ihRight right' hf.2.2 hs.2.2
                (hchange.mono (by omega) (by omega))
              cases heql
              exact ⟨steps, hsteps, hrot.rightContext _⟩
          · obtain ⟨old, new, ho, hn, hswitch⟩ :=
              hchange lo hi (by omega) (by omega) (by omega)
            have hminne : old ≠ new := by
              intro hsame
              subst new
              have hp := root_of_min hf ho
              have hq := root_of_min hs hn
              omega
            obtain ⟨hOld, hNew⟩ := hswitch.resolve_left hminne
            have ham : UniqueMin rank (2 * lo) (2 * hi) a := by simpa [hOld] using ho
            have hbm : UniqueMin rank' (2 * lo) (2 * hi) b := by simpa [hNew] using hn
            by_cases hpq : p < q
            · exact changed_roots left right left' right' hf hs hpq hchange ham hbm
            · obtain ⟨steps, hsteps, hrot⟩ := changed_roots left' right' left right
                hs hf (by omega) hchange.symm hbm ham
              exact ⟨steps, hsteps, hrot.symm⟩

end GreedyMerge.ProjectionRotation

#print axioms GreedyMerge.ProjectionRotation.changed_roots
#print axioms GreedyMerge.ProjectionRotation.projection_rotations

