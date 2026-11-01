import PlateauMinima

/-!
Substitution bridge for a canonical plateau. Abstract even atoms stand for
the true rank minima of full gap subtrees; odd atoms stand for real separator
keys. Replacing all null leaves of an indexed separator BST by these gap
subtrees preserves every expanded interval's minimum through this atom map.

The theorem is independent of the surface heights. The remaining surface
interface identifies these three-atom neighborhoods with strict neighborhoods.
-/

namespace GreedyMerge.GapExpansion

open Splay.Tree
open Splay.Tree.BST

def GapLower (separator : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => separator i + 1

def Expand (separator : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower separator i) (separator i))
    {lo hi : ℕ} : BST lo hi → BST (GapLower separator lo) (separator hi)
  | .empty i => gaps i
  | .node left right => .node (Expand separator gaps left) (Expand separator gaps right)

def AtomOwner (separator gapOwner : ℕ → ℕ) (atom : ℕ) : ℕ :=
  if atom % 2 = 0 then gapOwner (atom / 2) else 2 * separator (atom / 2) + 1

@[simp] theorem atomOwner_even (separator gapOwner : ℕ → ℕ) (i : ℕ) :
    AtomOwner separator gapOwner (2 * i) = gapOwner i := by
  have hdiv : (2 * i) / 2 = i := by omega
  have hmod : (2 * i) % 2 = 0 := by omega
  simp [AtomOwner, hdiv, hmod]

@[simp] theorem atomOwner_odd (separator gapOwner : ℕ → ℕ) (i : ℕ) :
    AtomOwner separator gapOwner (2 * i + 1) = 2 * separator i + 1 := by
  have hdiv : (2 * i + 1) / 2 = i := by omega
  have hmod : (2 * i + 1) % 2 = 1 := by omega
  simp [AtomOwner, hdiv, hmod]

theorem atomOwner_inside {lo hi atom : ℕ}
    (separator gapOwner : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower separator i) (separator i))
    (tree : BST lo hi)
    (gapInside : ∀ i, 2 * GapLower separator i ≤ gapOwner i ∧
      gapOwner i ≤ 2 * separator i)
    (hatomLo : 2 * lo ≤ atom) (hatomHi : atom ≤ 2 * hi) :
    2 * GapLower separator lo ≤ AtomOwner separator gapOwner atom ∧
      AtomOwner separator gapOwner atom ≤ 2 * separator hi := by
  induction tree generalizing atom with
  | empty i =>
      have heq : atom = 2 * i := by omega
      simpa [heq] using gapInside i
  | @node lo root hi left right ihLeft ihRight =>
      have leftBound := (Expand separator gaps left).lower_le_upper
      have rightBound := (Expand separator gaps right).lower_le_upper
      change separator root + 1 ≤ separator hi at rightBound
      by_cases hleft : atom ≤ 2 * root
      · have h := ihLeft hatomLo hleft
        exact ⟨h.1, by omega⟩
      · by_cases hroot : atom = 2 * root + 1
        · rw [hroot, atomOwner_odd]
          constructor <;> omega
        · have h := ihRight (by omega : 2 * (root + 1) ≤ atom) hatomHi
          change 2 * (separator root + 1) ≤ AtomOwner separator gapOwner atom ∧
            AtomOwner separator gapOwner atom ≤ 2 * separator hi at h
          exact ⟨by omega, h.2⟩

/-- A lower bound on all abstract atom ranks is a lower bound on every
actual external record in the substituted tree, including gap interiors. -/
theorem lower_bound_expands {lo hi bound : ℕ}
    (rank separator gapOwner : ℕ → ℕ)
    (tree : BST lo hi)
    (gapMin : ∀ i, IsIntervalMin rank (2 * GapLower separator i)
      (2 * separator i) (gapOwner i))
    (atomBound : ∀ atom, 2 * lo ≤ atom → atom ≤ 2 * hi →
      bound ≤ rank (AtomOwner separator gapOwner atom)) :
    ∀ position, 2 * GapLower separator lo ≤ position → position ≤ 2 * separator hi →
      bound ≤ rank position := by
  induction tree with
  | empty i =>
      intro position hposLo hposHi
      have hb := atomBound (2 * i) (Nat.le_refl _) (Nat.le_refl _)
      simp only [atomOwner_even] at hb
      exact Nat.le_trans hb ((gapMin i).2.2 position hposLo hposHi)
  | @node lo root hi left right ihLeft ihRight =>
      have hlo := left.lower_le_upper
      have hhi := right.lower_le_upper
      have atomLeft : ∀ atom, 2 * lo ≤ atom → atom ≤ 2 * root →
          bound ≤ rank (AtomOwner separator gapOwner atom) := by
        intro atom hal hau
        exact atomBound atom hal (by omega)
      have atomRight : ∀ atom, 2 * (root + 1) ≤ atom → atom ≤ 2 * hi →
          bound ≤ rank (AtomOwner separator gapOwner atom) := by
        intro atom hal hau
        exact atomBound atom (by omega) hau
      intro position hposLo hposHi
      by_cases hleft : position ≤ 2 * separator root
      · exact ihLeft atomLeft position hposLo hleft
      · by_cases hroot : position = 2 * separator root + 1
        · have hb := atomBound (2 * root + 1) (by omega) (by omega)
          simpa [hroot] using hb
        · apply ihRight atomRight position
          · change 2 * (separator root + 1) ≤ position
            omega
          · exact hposHi

/-- Every minimum of the abstract gap/value atom interval is exactly a
minimum of the full substituted interval under the atom-owner map. -/
theorem interval_min_expands {lo hi owner : ℕ}
    (rank separator gapOwner : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower separator i) (separator i))
    (tree : BST lo hi)
    (gapMin : ∀ i, IsIntervalMin rank (2 * GapLower separator i)
      (2 * separator i) (gapOwner i))
    (howner : IsIntervalMin (fun atom => rank (AtomOwner separator gapOwner atom))
      (2 * lo) (2 * hi) owner) :
    IsIntervalMin rank (2 * GapLower separator lo) (2 * separator hi)
      (AtomOwner separator gapOwner owner) := by
  have hinside := atomOwner_inside separator gapOwner gaps tree
    (fun i => ⟨(gapMin i).1, (gapMin i).2.1⟩) howner.1 howner.2.1
  refine ⟨hinside.1, hinside.2, ?_⟩
  exact lower_bound_expands rank separator gapOwner tree gapMin howner.2.2

/-- At a Cartesian separator root, its three-atom neighborhood owner is
the actual rank minimum of the complete expanded subtree. -/
theorem cartesian_root_min_expands {lo root hi owner : ℕ}
    (rank separator gapOwner : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower separator i) (separator i))
    (left : BST lo root) (right : BST (root + 1) hi)
    (gapMin : ∀ i, IsIntervalMin rank (2 * GapLower separator i)
      (2 * separator i) (gapOwner i))
    (hroot : ∀ key, lo ≤ key → key < hi →
      Plateau.Priority (fun atom => rank (AtomOwner separator gapOwner atom)) root ≤
        Plateau.Priority (fun atom => rank (AtomOwner separator gapOwner atom)) key)
    (howner : IsIntervalMin (fun atom => rank (AtomOwner separator gapOwner atom))
      (2 * root) (2 * root + 2) owner) :
    IsIntervalMin rank (2 * GapLower separator lo) (2 * separator hi)
      (AtomOwner separator gapOwner owner) := by
  apply interval_min_expands rank separator gapOwner gaps (.node left right) gapMin
  exact Plateau.local_min_is_full_min _ left right hroot howner

def ExpandedMinima (rank separator gapOwner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := root) left right =>
      (∀ owner, IsIntervalMin (fun atom => rank (AtomOwner separator gapOwner atom))
        (2 * root) (2 * root + 2) owner →
        IsIntervalMin rank (2 * GapLower separator lo) (2 * separator hi)
          (AtomOwner separator gapOwner owner)) ∧
      ExpandedMinima rank separator gapOwner left ∧
      ExpandedMinima rank separator gapOwner right

/-- The exact expanded minimum property holds simultaneously at every
separator node, not only at the top of the plateau skeleton. -/
theorem cartesian_all_minima_expand {lo hi : ℕ}
    (rank separator gapOwner : ℕ → ℕ)
    (gaps : ∀ i, BST (GapLower separator i) (separator i))
    (tree : BST lo hi)
    (gapMin : ∀ i, IsIntervalMin rank (2 * GapLower separator i)
      (2 * separator i) (gapOwner i))
    (hcart : Plateau.Cartesian
      (Plateau.Priority (fun atom => rank (AtomOwner separator gapOwner atom))) tree) :
    ExpandedMinima rank separator gapOwner tree := by
  induction tree with
  | empty => trivial
  | node left right ihLeft ihRight =>
      obtain ⟨hroot, hleft, hright⟩ := hcart
      refine ⟨?_, ihLeft hleft, ihRight hright⟩
      intro owner howner
      exact cartesian_root_min_expands rank separator gapOwner gaps
        left right gapMin hroot howner

end GreedyMerge.GapExpansion

#print axioms GreedyMerge.GapExpansion.cartesian_root_min_expands
#print axioms GreedyMerge.GapExpansion.cartesian_all_minima_expand
