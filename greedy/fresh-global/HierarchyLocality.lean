import PlateauBridge

/-!
Recursive ordered hierarchies and their canonical plateau refinements.
The hierarchy is fixed independently of comparator ranks. A surface's
multiway maximum-height hierarchy is a special case. Locality is proved
by recursion through the unique gap containing both rotated keys.
-/
namespace GreedyMerge.HierarchyLocality
open Splay.Tree
open Splay.Tree.BST
open GreedyMerge.IntervalRootOracle
open GreedyMerge.OrderedAtoms
open GreedyMerge.ComparatorAtoms
open GreedyMerge.ExpansionRotations
open GreedyMerge.PlateauBridge
open GreedyMerge.PortCases

/-- The finite children are the original lower gaps. The harmless linear
tail permits all-natural indexed substitution functions outside the node. -/
inductive Hierarchy : ℕ → ℕ → Type
  | empty (boundary : ℕ) : Hierarchy boundary boundary
  | node {start n : ℕ} (separator : ℕ → ℕ)
      (tail : ∀ i, n ≤ i → separator i = separator n + (i - n))
      (children : ∀ i, i ≤ n → Hierarchy (GapLower start separator i) (separator i)) :
      Hierarchy start (separator n)

/-- A concrete recursive realization. Atom minima and fixed-left-tie
separator refinement are certified at every hierarchy node. -/
def Realizes (rank : ℕ → ℕ) :
    {lo hi : ℕ} → Hierarchy lo hi → BST lo hi → Prop
  | _, _, .empty boundary, tree => tree = .empty boundary
  | _, _, .node (start := start) (n := n) separator _ children, tree =>
      ∃ (gaps : ∀ i, BST (GapLower start separator i) (separator i))
        (owner : ℕ → ℕ) (skeleton : BST 0 n),
        (∀ i (hi : i ≤ n), Realizes rank (children i hi) (gaps i)) ∧
        (∀ i, i ≤ n → UniqueMin rank (2 * GapLower start separator i)
          (2 * separator i) (owner i)) ∧
        Canonical (fun atom => rank (AtomOwner separator owner atom)) skeleton ∧
        tree = Expand start separator gaps skeleton

def RecordSame (rank rank' : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  RecordChanges rank rank' lo hi 0 0

theorem recordChanges_mono {rank rank' : ℕ → ℕ} {lo hi l u a b : ℕ}
    (h : RecordChanges rank rank' lo hi a b) (hl : lo ≤ l) (hu : u ≤ hi) :
    RecordChanges rank rank' l u a b := by
  intro x y hxl hxy hyu
  exact h x y (by omega) hxy (by omega)

theorem recordSame_of_excludes {rank rank' : ℕ → ℕ} {lo hi a b : ℕ}
    (h : RecordChanges rank rank' lo hi a b)
    (hex : a < lo ∨ hi < a ∨ b < lo ∨ hi < b) : RecordSame rank rank' lo hi := by
  intro l u hll hlu huu
  obtain ⟨old, new, ho, hn, hc⟩ := h l u hll hlu huu
  refine ⟨old, new, ho, hn, ?_⟩
  rcases hc with heq | ⟨ha, hb⟩
  · exact Or.inl heq
  · have hal := ho.1.1
    have hau := ho.1.2.1
    have hbl := hn.1.1
    have hbu := hn.1.2.1
    rcases hex with hx | hx | hx | hx <;> omega

theorem gap_bounds {start n i : ℕ} (separator : ℕ → ℕ)
    (gaps : ∀ j, BST (GapLower start separator j) (separator j)) (hi : i ≤ n) :
    start ≤ GapLower start separator i ∧ separator i ≤ separator n := by
  have hcut := cut_strictMono start separator gaps
  have hl := hcut.monotone (by omega : 0 ≤ 2 * i)
  have hu := hcut.monotone (by omega : 2 * i + 1 ≤ 2 * n + 1)
  rw [cut_zero, cut_even] at hl
  rw [cut_odd, cut_odd] at hu
  omega

/-- Full recursive shapes depend only on interval-minimum identities, even
when numeric ranks and representatives change at every hierarchy level. -/
theorem realizes_eq_of_recordSame {rank rank' : ℕ → ℕ} {lo hi : ℕ}
    (hierarchy : Hierarchy lo hi) (first second : BST lo hi)
    (hf : Realizes rank hierarchy first) (hs : Realizes rank' hierarchy second)
    (hsame : RecordSame rank rank' (2 * lo) (2 * hi)) : first = second := by
  induction hierarchy with
  | empty boundary =>
      change first = .empty boundary at hf
      change second = .empty boundary at hs
      rw [hf, hs]
  | @node start n separator tail children ih =>
      obtain ⟨gaps, owner, skeleton, subtrees, minima, canonical, hfirst⟩ := hf
      obtain ⟨gaps', owner', skeleton', subtrees', minima', canonical', hsecond⟩ := hs
      subst first
      subst second
      have hgaps : ∀ i, i ≤ n → gaps i = gaps' i := by
        intro i hi
        have hb := gap_bounds separator gaps hi
        exact ih i hi (gaps i) (gaps' i) (subtrees i hi) (subtrees' i hi)
          (recordChanges_mono hsame (by omega) (by omega))
      have hskeleton : skeleton = skeleton' := same_atom_projection_eq
        (cut_strictMono start separator gaps)
        (gap_owners_are_atom_owners minima) (gap_owners_are_atom_owners minima')
        (by simpa only [RecordSame, cut_zero, cut_odd, Nat.add_sub_cancel] using hsame)
        rfl skeleton skeleton' canonical canonical'
      subst skeleton'
      exact expand_eq_of_gaps_eq start separator gaps gaps' skeleton
        (fun i _ hi => hgaps i hi)

theorem realizes_eq_of_rotation_outside
    {treeLo treeHi lo hi a b depth : ℕ} {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (hierarchy : Hierarchy lo hi) (first second : BST lo hi)
    (hf : Realizes before.externalDepth hierarchy first)
    (hs : Realizes after.externalDepth hierarchy second)
    (hl : treeLo ≤ lo) (hu : hi ≤ treeHi)
    (hex : a < lo ∨ hi ≤ a ∨ b < lo ∨ hi ≤ b) : first = second := by
  apply realizes_eq_of_recordSame hierarchy first second hf hs
  apply recordSame_of_excludes
    (recordChanges_of_keyRotation step (by omega : 2 * treeLo ≤ 2 * lo)
      (by omega : 2 * hi ≤ 2 * treeHi))
  rcases hex with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem key_gap_unique {start key i j : ℕ} (separator : ℕ → ℕ)
    (gaps : ∀ k, BST (GapLower start separator k) (separator k))
    (hil : GapLower start separator i ≤ key) (hiu : key < separator i)
    (hjl : GapLower start separator j ≤ key) (hju : key < separator j) : i = j := by
  have hi := locate_key_in_gap separator gaps hil hiu
  have hj := locate_key_in_gap separator gaps hjl hju
  omega

/-- Sharp locality for the entire recursive ordered hierarchy. The proof
infers the unique relevant gap, proves all other recursive fringes fixed,
and stops at the first hierarchy node separating the comparator keys. -/
theorem hierarchy_rotation
    {treeLo treeHi lo hi a b depth : ℕ} {before after : BST treeLo treeHi}
    (step : GreedyMerge.KeyRotationAt a b depth before after)
    (hierarchy : Hierarchy lo hi) (first second : BST lo hi)
    (hf : Realizes before.externalDepth hierarchy first)
    (hs : Realizes after.externalDepth hierarchy second)
    (hl : treeLo ≤ lo) (hu : hi ≤ treeHi) :
    ∃ steps, steps ≤ 2 ∧ RotationSteps steps first second := by
  induction hierarchy with
  | empty boundary =>
      change first = .empty boundary at hf
      change second = .empty boundary at hs
      rw [hf, hs]
      exact ⟨0, by omega, .refl _⟩
  | @node start n separator tail children ih =>
      obtain ⟨gaps, owner, skeleton, subtrees, minima, canonical, hfirst⟩ := hf
      obtain ⟨gaps', owner', skeleton', subtrees', minima', canonical', hsecond⟩ := hs
      subst first
      subst second
      by_cases hshared : ∃ i, i ≤ n ∧
          GapLower start separator i ≤ a ∧ a < separator i ∧
          GapLower start separator i ≤ b ∧ b < separator i
      · obtain ⟨key, hkey, hal, hau, hbl, hbu⟩ := hshared
        have hbounds := gap_bounds separator gaps hkey
        obtain ⟨steps, hsteps, hrot⟩ := ih key hkey (gaps key) (gaps' key)
          (subtrees key hkey) (subtrees' key hkey) (by omega) (by omega)
        have heq : ∀ i, i ≤ n → i ≠ key → gaps i = gaps' i := by
          intro i hi hne
          have hibounds := gap_bounds separator gaps hi
          have houtside : a < GapLower start separator i ∨ separator i ≤ a := by
            by_cases hil : GapLower start separator i ≤ a
            · right
              by_contra hin
              have heq := key_gap_unique separator gaps hil (by omega) hal hau
              exact hne heq
            · exact Or.inl (by omega)
          apply realizes_eq_of_rotation_outside step (children i hi) (gaps i) (gaps' i)
            (subtrees i hi) (subtrees' i hi) (by omega) (by omega)
          rcases houtside with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        exact ⟨steps, hsteps, plateau_one_changed_gap step separator owner owner'
          gaps gaps' hl hu hkey hal hau hbl hbu minima minima'
          skeleton skeleton' canonical canonical' heq hrot⟩
      · have heq : ∀ i, i ≤ n → gaps i = gaps' i := by
          intro i hi
          have hibounds := gap_bounds separator gaps hi
          have hnoboth : ¬(GapLower start separator i ≤ a ∧ a < separator i ∧
              GapLower start separator i ≤ b ∧ b < separator i) := by
            intro h
            exact hshared ⟨i, hi, h⟩
          apply realizes_eq_of_rotation_outside step (children i hi) (gaps i) (gaps' i)
            (subtrees i hi) (subtrees' i hi) (by omega) (by omega)
          omega
        obtain ⟨steps, hsteps, hrot⟩ := plateau_rotation_with_fixed_gaps step
          separator owner owner' gaps hl hu minima minima' skeleton skeleton' canonical canonical'
        refine ⟨steps, hsteps, ?_⟩
        have hexpand := expand_eq_of_gaps_eq start separator gaps gaps' skeleton'
          (fun i _ hi => heq i hi)
        rw [← hexpand]
        exact hrot

end GreedyMerge.HierarchyLocality

#print axioms GreedyMerge.HierarchyLocality.realizes_eq_of_recordSame

#print axioms GreedyMerge.HierarchyLocality.hierarchy_rotation
