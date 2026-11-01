import Mathlib
import PlateauMinima
import IntervalRootOracle

/-!
The heap of a canonical separator projection. Even atoms are gap minima;
odd atoms are separator values. The heap children below are derived by
contracting minimum-owner ternary paths, not supplied as a Cartesian
forest hypothesis. Full gap substitution is the separate GapExpansion
interface.
-/

namespace GreedyMerge.Fringe

open Splay.Tree Splay.Tree.BST
open GreedyMerge.IntervalRootOracle (UniqueMin)

def LocalOwners (rank owner : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∀ q, lo ≤ q → q < hi → UniqueMin rank (2*q) (2*q+2) (owner q)

def UniqueIntervals (rank : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∀ l u a b, lo ≤ l → u ≤ hi →
    IsIntervalMin rank l u a → IsIntervalMin rank l u b → a=b

def treeOwner (owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → ℕ
  | .empty i => 2*i
  | .node (root := q) _ _ => owner q

def Projection (rank owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Prop
  | .empty _ => True
  | .node (root := q) left right =>
      UniqueMin rank (2*lo) (2*hi) (owner q) ∧
        Projection rank owner left ∧ Projection rank owner right

theorem unique_of_min {rank : ℕ → ℕ} {lo hi owner : ℕ}
    (hmin : IsIntervalMin rank lo hi owner)
    (hunique : ∀ a b, IsIntervalMin rank lo hi a →
      IsIntervalMin rank lo hi b → a=b) : UniqueMin rank lo hi owner := by
  refine ⟨hmin, ?_⟩
  intro other hl hu hne
  have hle := hmin.2.2 other hl hu
  by_contra hnot
  have hother : IsIntervalMin rank lo hi other := by
    refine ⟨hl,hu,?_⟩
    intro key hkl hku
    have hk := hmin.2.2 key hkl hku
    omega
  exact hne (hunique other owner hother hmin)

/-- Exact projection is derived from the canonical neighborhood priorities
and uniqueness of interval minima. No heap shape is assumed. -/
theorem projection_of_cartesian {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi)
    (hcan : GreedyMerge.Plateau.Cartesian (GreedyMerge.Plateau.Priority rank) tree)
    (hloc : LocalOwners rank owner lo hi)
    (hunique : UniqueIntervals rank (2*lo) (2*hi)) :
    Projection rank owner tree := by
  induction tree with
  | empty => trivial
  | @node lo root hi left right ihLeft ihRight =>
      obtain ⟨hroot,hleft,hright⟩ := hcan
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hown := hloc root hl (by omega)
      have hfull := GreedyMerge.Plateau.local_min_is_full_min rank left right hroot hown.1
      refine ⟨unique_of_min hfull (by intro a b ha hb; exact hunique _ _ a b (by omega) (by omega) ha hb), ?_, ?_⟩
      · apply ihLeft hleft
        · intro q hql hqu;exact hloc q hql (by omega)
        · intro l u a b hll huu ha hb
          exact hunique l u a b hll (by omega) ha hb
      · apply ihRight hright
        · intro q hql hqu;exact hloc q (by omega) hqu
        · intro l u a b hll huu ha hb
          exact hunique l u a b (by omega) huu ha hb

theorem treeOwner_min {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (h : Projection rank owner tree) :
    UniqueMin rank (2*lo) (2*hi) (treeOwner owner tree) := by
  cases tree with
  | empty =>
      simp only [treeOwner]
      refine ⟨⟨by omega,by omega,?_⟩,?_⟩
      · intro key hl hu;have heq : key=2*lo := by omega
        simp [heq]
      · intro key hl hu hne
        omega
  | node left right =>exact h.1

theorem treeOwner_bounds {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (h : Projection rank owner tree) :
    2*lo ≤ treeOwner owner tree ∧ treeOwner owner tree ≤ 2*hi :=
  ⟨(treeOwner_min rank owner tree h).1.1,(treeOwner_min rank owner tree h).1.2.1⟩

theorem child_owner_eq {rank : ℕ → ℕ} {lo hi l u p c : ℕ}
    (hbig : UniqueMin rank lo hi p) (hchild : IsIntervalMin rank l u c)
    (hlo : lo ≤ l) (hhi : u ≤ hi) (hpl : l ≤ p) (hpu : p ≤ u) : c=p := by
  by_contra hne
  have hstrict := hbig.2 c (by have := hchild.1;omega)
    (by have := hchild.2.1;omega) hne
  have hle := hchild.2.2 p hpl hpu
  omega

theorem owner_cases {rank owner : ℕ → ℕ} {lo hi q : ℕ}
    (hloc : LocalOwners rank owner lo hi) (hql : lo ≤ q) (hqu : q < hi) :
    owner q = 2*q ∨ owner q = 2*q+1 ∨ owner q = 2*q+2 := by
  have hl := (hloc q hql hqu).1.1
  have hu := (hloc q hql hqu).1.2.1
  omega

def Retained (owner : ℕ → ℕ) (atom : ℕ) : Prop :=
  atom % 2 = 0 ∨ owner (atom/2) = atom

instance retainedDecidable (owner : ℕ → ℕ) (atom : ℕ) :
    Decidable (Retained owner atom) := inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem retained_even (owner : ℕ → ℕ) (q : ℕ) : Retained owner (2*q) := by
  left;omega

@[simp] theorem retained_odd (owner : ℕ → ℕ) (q : ℕ) :
    Retained owner (2*q+1) ↔ owner q=2*q+1 := by
  have hd : (2*q+1)/2=q := by omega
  have hm : (2*q+1)%2=1 := by omega
  simp [Retained,hd,hm]

theorem owner_retained {rank owner : ℕ → ℕ} {lo hi q : ℕ}
    (hloc : LocalOwners rank owner lo hi) (hql : lo ≤ q) (hqu : q < hi) :
    Retained owner (owner q) := by
  rcases owner_cases hloc hql hqu with h | h | h
  · rw [h];exact retained_even owner q
  · rw [h];exact (retained_odd owner q).2 h
  · have hh : 2*q+2=2*(q+1) := by omega
    rw [h,hh];exact retained_even owner (q+1)

theorem treeOwner_retained {rank owner : ℕ → ℕ} {lo hi : ℕ}
    (tree : BST lo hi) (hloc : LocalOwners rank owner lo hi) :
    Retained owner (treeOwner owner tree) := by
  cases tree with
  | empty =>exact retained_even owner lo
  | @node lo q hi left right =>
      exact owner_retained hloc left.lower_le_upper (by have := right.lower_le_upper;omega)

def localChildren (owner : ℕ → ℕ) {lo q hi : ℕ}
    (left : BST lo q) (right : BST (q+1) hi) : List ℕ :=
  [treeOwner owner left,2*q+1,treeOwner owner right].filter (fun v => v != owner q)

/-- This is the actual contraction rule: each ternary node connects its
two light ports to its minimum-owner record; heavy self-edges disappear. -/
def outgoing (owner : ℕ → ℕ) (parent : ℕ) {lo hi : ℕ} : BST lo hi → List ℕ
  | .empty _ => []
  | .node (root := q) left right =>
      outgoing owner parent left ++ outgoing owner parent right ++
        if owner q=parent then localChildren owner left right else []

theorem local_children_cases {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (owner q=2*q ∧ treeOwner owner left=2*q ∧
      localChildren owner left right=[2*q+1,treeOwner owner right]) ∨
    (owner q=2*q+1 ∧
      localChildren owner left right=[treeOwner owner left,treeOwner owner right]) ∨
    (owner q=2*q+2 ∧ treeOwner owner right=2*q+2 ∧
      localChildren owner left right=[treeOwner owner left,2*q+1]) := by
  have hl := left.lower_le_upper
  have hr := right.lower_le_upper
  have leftMin := treeOwner_min rank owner left hproj.2.1
  have rightMin := treeOwner_min rank owner right hproj.2.2
  have leftBound := treeOwner_bounds rank owner left hproj.2.1
  have rightBound := treeOwner_bounds rank owner right hproj.2.2
  rcases owner_cases hloc hl (by omega) with h | h | h
  · have heq : treeOwner owner left=2*q := by
      have hh := child_owner_eq hproj.1 leftMin.1 (by omega) (by omega)
        (by omega : 2*lo ≤ owner q) (by omega : owner q ≤ 2*q)
      omega
    refine Or.inl ⟨h,heq,?_⟩
    have hright : treeOwner owner right ≠ 2*q := by omega
    simp [localChildren,heq,h,hright]
  · refine Or.inr (Or.inl ⟨h,?_⟩)
    have hleft : treeOwner owner left ≠ 2*q+1 := by omega
    have hright : treeOwner owner right ≠ 2*q+1 := by omega
    simp [localChildren,h,hleft,hright]
  · have heq : treeOwner owner right=2*q+2 := by
      have hh := child_owner_eq hproj.1 rightMin.1 (by omega) (by omega)
        (by omega : 2*(q+1) ≤ owner q) (by omega : owner q ≤ 2*hi)
      omega
    refine Or.inr (Or.inr ⟨h,heq,?_⟩)
    have hleft : treeOwner owner left ≠ 2*q+2 := by omega
    simp [localChildren,heq,h,hleft]

theorem local_children_length {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (localChildren owner left right).length=2 := by
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · simp [h.2.2]
  · simp [h.2]
  · simp [h.2.2]

def countKeys (pred : ℕ → Prop) [DecidablePred pred] {lo hi : ℕ} : BST lo hi → ℕ
  | .empty _ => 0
  | .node (root := q) left right =>
      (if pred q then 1 else 0) + countKeys pred left + countKeys pred right

theorem countKeys_mono {lo hi : ℕ} (tree : BST lo hi)
    (first second : ℕ → Prop) [DecidablePred first] [DecidablePred second]
    (h : ∀ q, lo ≤ q → q < hi → first q → second q) :
    countKeys first tree ≤ countKeys second tree := by
  induction tree with
  | empty => rfl
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hq := h q hl (by omega)
      have hleft := ihLeft (by intro k hkl hku;exact h k hkl (by omega))
      have hright := ihRight (by intro k hkl hku;exact h k (by omega) hku)
      simp only [countKeys]
      split_ifs <;> simp_all <;> omega

theorem countKeys_or_le {lo hi : ℕ} (tree : BST lo hi)
    (first second : ℕ → Prop) [DecidablePred first] [DecidablePred second] :
    countKeys (fun q => first q ∨ second q) tree ≤
      countKeys first tree + countKeys second tree := by
  induction tree with
  | empty => rfl
  | @node lo q hi left right ihLeft ihRight =>
      simp only [countKeys]
      split_ifs <;> simp_all <;> omega

theorem countKeys_key {lo hi : ℕ} (tree : BST lo hi) (key : ℕ) :
    countKeys (fun q => q=key) tree = if lo ≤ key ∧ key < hi then 1 else 0 := by
  induction tree with
  | empty =>simp [countKeys]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      simp only [countKeys,ihLeft,ihRight]
      split_ifs <;> omega

theorem countKeys_key_le_one {lo hi : ℕ} (tree : BST lo hi) (key : ℕ) :
    countKeys (fun q => q=key) tree ≤ 1 := by
  rw [countKeys_key]
  split_ifs <;> omega

/-- An atom can own only its two incident separator positions. For an odd
atom those two arithmetic positions coincide. -/
theorem owned_separator_count_le_two {lo hi : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi) (parent : ℕ)
    (hloc : LocalOwners rank owner lo hi) :
    countKeys (fun q => owner q=parent) tree ≤ 2 := by
  have hm := countKeys_mono tree (fun q => owner q=parent)
    (fun q => q=parent/2 ∨ q=(parent-1)/2) (by
      intro q hql hqu heq
      have hlow := (hloc q hql hqu).1.1
      have hupp := (hloc q hql hqu).1.2.1
      omega)
  have ho := countKeys_or_le tree (fun q => q=parent/2) (fun q => q=(parent-1)/2)
  have hfirst := countKeys_key_le_one tree (parent/2)
  have hsecond := countKeys_key_le_one tree ((parent-1)/2)
  omega

theorem outgoing_length_eq_twice_owned {lo hi : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (outgoing owner parent tree).length =
      2 * countKeys (fun q => owner q=parent) tree := by
  induction tree with
  | empty =>rfl
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku)
      have hlocal := local_children_length rank owner left right hproj hloc
      simp only [outgoing,List.length_append,countKeys]
      split_ifs <;> simp_all <;> omega

/-- The degree-four statement is derived from the canonical projection;
it is not supplied as a forest axiom. -/
theorem outgoing_degree_le_four {lo hi : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (outgoing owner parent tree).length ≤ 4 := by
  rw [outgoing_length_eq_twice_owned rank owner tree parent hproj hloc]
  have h := owned_separator_count_le_two rank owner tree parent hloc
  omega

def leftRetained (owner : ℕ → ℕ) (parent : ℕ) (children : List ℕ) : List ℕ :=
  children.filter (fun v => decide (Retained owner v ∧ v < parent))

def rightRetained (owner : ℕ → ℕ) (parent : ℕ) (children : List ℕ) : List ℕ :=
  children.filter (fun v => decide (Retained owner v ∧ parent < v))

theorem local_left_retained_bound {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (leftRetained owner (owner q) (localChildren owner left right)).length ≤
      if q=(owner q-1)/2 then 1 else 0 := by
  have hl := left.lower_le_upper
  have hr := right.lower_le_upper
  have hleft := treeOwner_retained left (by intro k hkl hku;exact hloc k hkl (by omega))
  have hright := treeOwner_retained right (by intro k hkl hku;exact hloc k (by omega) hku)
  have leftBound := treeOwner_bounds rank owner left hproj.2.1
  have rightBound := treeOwner_bounds rank owner right hproj.2.2
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · have hv : ¬Retained owner (2*q+1) := by
      rw [retained_odd];omega
    have hn : ¬treeOwner owner right < owner q := by omega
    have hval : owner q ≠ 2*q+1 := by omega
    simp [leftRetained,h.2.2,hval,hn]
  · have hy : treeOwner owner left < owner q := by omega
    have hn : ¬treeOwner owner right < owner q := by omega
    have hdiv : q=(owner q-1)/2 := by omega
    rw [if_pos hdiv]
    simp [leftRetained,h.2,hleft,hright,hy,hn]
  · have hv : ¬Retained owner (2*q+1) := by
      rw [retained_odd];omega
    have hy : treeOwner owner left < owner q := by omega
    have hdiv : q=(owner q-1)/2 := by omega
    rw [if_pos hdiv]
    have hval : owner q ≠ 2*q+1 := by omega
    simp [leftRetained,h.2.2,hleft,hval,hy]

theorem local_right_retained_bound {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (rightRetained owner (owner q) (localChildren owner left right)).length ≤
      if q=owner q/2 then 1 else 0 := by
  have hl := left.lower_le_upper
  have hr := right.lower_le_upper
  have hleft := treeOwner_retained left (by intro k hkl hku;exact hloc k hkl (by omega))
  have hright := treeOwner_retained right (by intro k hkl hku;exact hloc k (by omega) hku)
  have leftBound := treeOwner_bounds rank owner left hproj.2.1
  have rightBound := treeOwner_bounds rank owner right hproj.2.2
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · have hv : ¬Retained owner (2*q+1) := by
      rw [retained_odd];omega
    have hy : owner q < treeOwner owner right := by omega
    have hdiv : q=owner q/2 := by omega
    rw [if_pos hdiv]
    have hval : owner q ≠ 2*q+1 := by omega
    simp [rightRetained,h.2.2,hright,hval,hy]
  · have hn : ¬owner q < treeOwner owner left := by omega
    have hy : owner q < treeOwner owner right := by omega
    have hdiv : q=owner q/2 := by omega
    rw [if_pos hdiv]
    simp [rightRetained,h.2,hleft,hright,hy,hn]
  · have hv : ¬Retained owner (2*q+1) := by
      rw [retained_odd];omega
    have hn : ¬owner q < treeOwner owner left := by omega
    have hval : owner q ≠ 2*q+1 := by omega
    simp [rightRetained,h.2.2,hval,hn]

theorem left_retained_length_le_key_count {lo hi : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (leftRetained owner parent (outgoing owner parent tree)).length ≤
      countKeys (fun q => q=(parent-1)/2) tree := by
  induction tree with
  | empty =>simp [leftRetained,outgoing,countKeys]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku)
      have hlocal := local_left_retained_bound rank owner left right hproj hloc
      by_cases hp : owner q=parent
      · rw [hp] at hlocal
        simp only [outgoing,if_pos hp,leftRetained,List.filter_append,List.length_append,countKeys]
        change (leftRetained owner parent (outgoing owner parent left)).length +
          (leftRetained owner parent (outgoing owner parent right)).length +
          (leftRetained owner parent (localChildren owner left right)).length ≤ _
        omega
      · simp only [outgoing,if_neg hp,leftRetained,List.filter_append,List.length_append,
          List.filter_nil,List.length_nil,countKeys]
        change (leftRetained owner parent (outgoing owner parent left)).length +
          (leftRetained owner parent (outgoing owner parent right)).length + 0 ≤ _
        split_ifs <;> omega

theorem right_retained_length_le_key_count {lo hi : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (rightRetained owner parent (outgoing owner parent tree)).length ≤
      countKeys (fun q => q=parent/2) tree := by
  induction tree with
  | empty =>simp [rightRetained,outgoing,countKeys]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku)
      have hlocal := local_right_retained_bound rank owner left right hproj hloc
      by_cases hp : owner q=parent
      · rw [hp] at hlocal
        simp only [outgoing,if_pos hp,rightRetained,List.filter_append,List.length_append,countKeys]
        change (rightRetained owner parent (outgoing owner parent left)).length +
          (rightRetained owner parent (outgoing owner parent right)).length +
          (rightRetained owner parent (localChildren owner left right)).length ≤ _
        omega
      · simp only [outgoing,if_neg hp,rightRetained,List.filter_append,List.length_append,
          List.filter_nil,List.length_nil,countKeys]
        change (rightRetained owner parent (outgoing owner parent left)).length +
          (rightRetained owner parent (outgoing owner parent right)).length + 0 ≤ _
        split_ifs <;> omega

/-- Pruning inactive values leaves at most one child on either side:
the retained graph is binary in search order, as derived from projection. -/
theorem retained_binary_degree {lo hi : ℕ}
    (rank owner : ℕ → ℕ) (tree : BST lo hi) (parent : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (leftRetained owner parent (outgoing owner parent tree)).length ≤ 1 ∧
    (rightRetained owner parent (outgoing owner parent tree)).length ≤ 1 := by
  constructor
  · exact (left_retained_length_le_key_count rank owner tree parent hproj hloc).trans
      (countKeys_key_le_one tree ((parent-1)/2))
  · exact (right_retained_length_le_key_count rank owner tree parent hproj hloc).trans
      (countKeys_key_le_one tree (parent/2))

/-- An inactive value owns no separator, hence has no projected children. -/
theorem inactive_outgoing_empty {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (atom : ℕ) (hinactive : ¬Retained owner atom)
    (hloc : LocalOwners rank owner lo hi) : outgoing owner atom tree = [] := by
  induction tree with
  | empty => rfl
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hp : owner q ≠ atom := by
        intro heq
        exact hinactive (heq ▸ owner_retained hloc hl (by omega))
      have hleft := ihLeft (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight (by intro k hkl hku;exact hloc k (by omega) hku)
      simp [outgoing,hp,hleft,hright]

theorem inactive_local_member {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi) (atom : ℕ)
    (hinactive : ¬Retained owner atom)
    (hloc : LocalOwners rank owner lo hi) :
    atom ∈ localChildren owner left right ↔ atom=2*q+1 := by
  have hl := left.lower_le_upper
  have hr := right.lower_le_upper
  have hleft := treeOwner_retained left (by intro k hkl hku;exact hloc k hkl (by omega))
  have hright := treeOwner_retained right (by intro k hkl hku;exact hloc k (by omega) hku)
  have hown := owner_retained hloc hl (by omega)
  have hnleft : atom ≠ treeOwner owner left := by intro h;exact hinactive (h ▸ hleft)
  have hnright : atom ≠ treeOwner owner right := by intro h;exact hinactive (h ▸ hright)
  have hnown : atom ≠ owner q := by intro h;exact hinactive (h ▸ hown)
  simp [localChildren,hnleft,hnright,hnown]

/-- The parent of an inactive odd value is exactly its neighborhood minimum.
This is a statement about the actual contracted edge list. -/
theorem inactive_parent_exact {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (parent i : ℕ) (hinactive : ¬Retained owner (2*i+1))
    (hloc : LocalOwners rank owner lo hi) :
    2*i+1 ∈ outgoing owner parent tree ↔ lo ≤ i ∧ i < hi ∧ parent=owner i := by
  induction tree with
  | empty => simp [outgoing];omega
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight (by intro k hkl hku;exact hloc k (by omega) hku)
      have hlocal := inactive_local_member rank owner left right (2*i+1) hinactive hloc
      simp only [outgoing,List.mem_append]
      rw [hleft,hright]
      by_cases hp : owner q=parent
      · simp only [if_pos hp,hlocal]
        constructor
        · rintro ((h | h) | heq)
          · exact ⟨h.1,by omega,h.2.2⟩
          · exact ⟨by omega,h.2.1,h.2.2⟩
          · have hiq : i=q := by omega
            subst i
            exact ⟨hl,by omega,hp.symm⟩
        · rintro ⟨hli,hih,hp⟩
          by_cases hil : i < q
          · exact Or.inl (Or.inl ⟨hli,hil,hp⟩)
          · by_cases hir : q < i
            · exact Or.inl (Or.inr ⟨by omega,hih,hp⟩)
            · right;omega
      · simp only [if_neg hp,List.not_mem_nil,or_false]
        constructor
        · rintro (h | h)
          · exact ⟨h.1,by omega,h.2.2⟩
          · exact ⟨by omega,h.2.1,h.2.2⟩
        · rintro ⟨hli,hih,hpi⟩
          have hne : i≠q := by intro h;subst i;exact hp hpi.symm
          by_cases hil : i < q
          · exact Or.inl ⟨hli,hil,hpi⟩
          · exact Or.inr ⟨by omega,hih,hpi⟩

/-- The inactive parent is the strictly better-ranked adjacent gap. -/
theorem inactive_parent_is_gap {rank owner : ℕ → ℕ} {lo hi i : ℕ}
    (hloc : LocalOwners rank owner lo hi) (hli : lo ≤ i) (hih : i < hi)
    (hinactive : ¬Retained owner (2*i+1)) :
    (owner i=2*i ∨ owner i=2*i+2) ∧ rank (owner i)<rank (2*i+1) := by
  have hv : owner i≠2*i+1 := by simpa using hinactive
  constructor
  · rcases owner_cases hloc hli hih with h | h | h
    · exact Or.inl h
    · exact False.elim (hv h)
    · exact Or.inr h
  · exact (hloc i hli hih).2 (2*i+1) (by omega) (by omega) (Ne.symm hv)

def edges (owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → List (ℕ × ℕ)
  | .empty _ => []
  | .node (root := q) left right =>
      edges owner left ++ edges owner right ++
        (localChildren owner left right).map (fun child => (owner q,child))

theorem mem_edges_iff_outgoing {lo hi : ℕ} (owner : ℕ → ℕ)
    (tree : BST lo hi) (parent child : ℕ) :
    (parent,child) ∈ edges owner tree ↔ child ∈ outgoing owner parent tree := by
  induction tree with
  | empty =>simp [edges,outgoing]
  | @node lo q hi left right ihLeft ihRight =>
      simp only [edges,outgoing,List.mem_append,List.mem_map,Prod.mk.injEq]
      rw [ihLeft,ihRight]
      by_cases hp : owner q=parent
      · simp [hp]
      · simp [hp]

theorem edge_strict_rank_and_bounds {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (parent child : ℕ)
    (hproj : Projection rank owner tree)
    (hedge : (parent,child) ∈ edges owner tree) :
    2*lo ≤ parent ∧ parent ≤ 2*hi ∧ 2*lo ≤ child ∧ child ≤ 2*hi ∧
      rank parent < rank child := by
  induction tree with
  | empty =>simp [edges] at hedge
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      simp only [edges,List.mem_append,List.mem_map,Prod.mk.injEq] at hedge
      rcases hedge with (h | h) | ⟨v,hv,hparent,hchild⟩
      · have h := ihLeft hproj.2.1 h
        exact ⟨h.1,by omega,h.2.2.1,by omega,h.2.2.2.2⟩
      · have h := ihRight hproj.2.2 h
        exact ⟨by omega,h.2.1,by omega,h.2.2.2.1,h.2.2.2.2⟩
      · subst parent;subst child
        have leftBound := treeOwner_bounds rank owner left hproj.2.1
        have rightBound := treeOwner_bounds rank owner right hproj.2.2
        simp only [localChildren,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false,
          bne_iff_ne,ne_eq] at hv
        have hvl : 2*lo ≤ v := by rcases hv.1 with h|h|h <;> omega
        have hvu : v ≤ 2*hi := by rcases hv.1 with h|h|h <;> omega
        exact ⟨hproj.1.1.1,hproj.1.1.2.1,hvl,hvu,hproj.1.2 v hvl hvu hv.2⟩

def oneAt (target atom : ℕ) : ℕ := if atom=target then 1 else 0

def incoming (owner : ℕ → ℕ) {lo hi : ℕ} (tree : BST lo hi) (atom : ℕ) : ℕ :=
  (edges owner tree).countP (fun edge => edge.2 == atom)

theorem local_incoming_balance {lo q hi : ℕ} (rank owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi) (atom : ℕ)
    (hproj : Projection rank owner (.node left right))
    (hloc : LocalOwners rank owner lo hi) :
    (localChildren owner left right).countP (fun child => child == atom) +
      oneAt atom (owner q) =
      oneAt atom (treeOwner owner left) + oneAt atom (2*q+1) +
        oneAt atom (treeOwner owner right) := by
  rcases local_children_cases rank owner left right hproj hloc with h | h | h
  · simp [h.2.2,h.1,h.2.1,oneAt,List.countP_cons];omega
  · simp [h.2,h.1,oneAt,List.countP_cons];omega
  · simp [h.2.2,h.1,h.2.1,oneAt,List.countP_cons];omega

/-- Every atom except the projected root has exactly one incoming edge,
and the root has none. Outside atoms have no incoming edge. -/
theorem incoming_balance {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (atom : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    incoming owner tree atom + oneAt atom (treeOwner owner tree) =
      if 2*lo ≤ atom ∧ atom ≤ 2*hi then 1 else 0 := by
  induction tree with
  | empty =>
      simp only [incoming,edges,List.countP_nil,treeOwner,zero_add,oneAt]
      split_ifs <;> omega
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hleft := ihLeft hproj.2.1 (by intro k hkl hku;exact hloc k hkl (by omega))
      have hright := ihRight hproj.2.2 (by intro k hkl hku;exact hloc k (by omega) hku)
      have hlocal := local_incoming_balance rank owner left right atom hproj hloc
      have hinterval : (if 2*lo ≤ atom ∧ atom ≤ 2*hi then 1 else 0) =
          (if 2*lo ≤ atom ∧ atom ≤ 2*q then 1 else 0) + oneAt atom (2*q+1) +
          (if 2*(q+1) ≤ atom ∧ atom ≤ 2*hi then 1 else 0) := by
        simp only [oneAt]
        split_ifs <;> omega
      simp only [incoming,edges,List.countP_append,List.countP_map,Function.comp_def,
        treeOwner]
      change incoming owner left atom + incoming owner right atom +
        (localChildren owner left right).countP (fun child => child == atom) +
        oneAt atom (owner q) = _
      omega

theorem incoming_nonroot_eq_one {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (atom : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (hal : 2*lo ≤ atom) (hau : atom ≤ 2*hi)
    (hne : atom≠treeOwner owner tree) : incoming owner tree atom=1 := by
  have h := incoming_balance rank owner tree atom hproj hloc
  simpa [oneAt,Ne.symm hne,hal,hau] using h

theorem incoming_root_eq_zero {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    incoming owner tree (treeOwner owner tree)=0 := by
  have h := incoming_balance rank owner tree (treeOwner owner tree) hproj hloc
  have hb := treeOwner_bounds rank owner tree hproj
  simp only [oneAt,hb.1,hb.2,and_self,if_true] at h
  omega

theorem incoming_parent_exists {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (atom : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (hal : 2*lo ≤ atom) (hau : atom ≤ 2*hi)
    (hne : atom≠treeOwner owner tree) :
    ∃ parent, (parent,atom) ∈ edges owner tree := by
  have hcount := incoming_nonroot_eq_one rank owner tree atom hproj hloc hal hau hne
  have hpos : 0 < (edges owner tree).countP (fun edge => edge.2 == atom) := by
    change 0 < incoming owner tree atom
    omega
  obtain ⟨⟨parent,child⟩,hmem,hchild⟩ := List.countP_pos_iff.mp hpos
  have hc : child=atom := by simpa using hchild
  exact ⟨parent,hc ▸ hmem⟩

/-- Actual projection edges connect every external atom to the global root.
The proof uses strict rank descent and the derived incoming-edge identity. -/
theorem projection_root_reaches {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (atom : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (hal : 2*lo ≤ atom) (hau : atom ≤ 2*hi) :
    Relation.ReflTransGen (fun a b => (a,b) ∈ edges owner tree)
      (treeOwner owner tree) atom := by
  generalize hn : rank atom=n
  induction n using Nat.strong_induction_on generalizing atom with
  | h n ih =>
      by_cases heq : atom=treeOwner owner tree
      · subst atom;exact Relation.ReflTransGen.refl
      · obtain ⟨parent,hparent⟩ := incoming_parent_exists rank owner tree atom hproj hloc hal hau heq
        have he := edge_strict_rank_and_bounds rank owner tree parent atom hproj hparent
        have hp := ih (rank parent) (by omega) parent he.1 he.2.1 rfl
        exact hp.tail hparent

/-- Every projected edge satisfies the interval minimum oracle on the
closed key interval between its two endpoints. -/
theorem edge_min_between {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (parent child : ℕ)
    (hproj : Projection rank owner tree)
    (hedge : (parent,child) ∈ edges owner tree) :
    IsIntervalMin rank (min parent child) (max parent child) parent := by
  induction tree with
  | empty =>simp [edges] at hedge
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      simp only [edges,List.mem_append,List.mem_map,Prod.mk.injEq] at hedge
      rcases hedge with (h | h) | ⟨v,hv,hparent,hchild⟩
      · exact ihLeft hproj.2.1 h
      · exact ihRight hproj.2.2 h
      · subst parent;subst child
        have leftBound := treeOwner_bounds rank owner left hproj.2.1
        have rightBound := treeOwner_bounds rank owner right hproj.2.2
        simp only [localChildren,List.mem_filter,List.mem_cons,List.not_mem_nil,or_false,
          bne_iff_ne,ne_eq] at hv
        have hvl : 2*lo ≤ v := by rcases hv.1 with h|h|h <;> omega
        have hvu : v ≤ 2*hi := by rcases hv.1 with h|h|h <;> omega
        have hpl := hproj.1.1.1
        have hpu := hproj.1.1.2.1
        refine ⟨by omega,by omega,?_⟩
        intro key hkl hku
        exact hproj.1.1.2.2 key (by omega) (by omega)

theorem projected_descendants_stay_left {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (ancestor start target : ℕ)
    (hproj : Projection rank owner tree)
    (hleft : start < ancestor) (hrank : rank ancestor < rank start)
    (hpath : Relation.ReflTransGen (fun a b => (a,b) ∈ edges owner tree) start target) :
    target < ancestor ∧ rank ancestor < rank target := by
  induction hpath with
  | refl => exact ⟨hleft,hrank⟩
  | @tail previous target hprefix hedge ih =>
      have hbetween := edge_min_between rank owner tree previous target hproj hedge
      have hstrict := (edge_strict_rank_and_bounds rank owner tree previous target hproj hedge).2.2.2.2
      constructor
      · by_contra hnot
        have hmin := hbetween.2.2 ancestor (by omega) (by omega)
        omega
      · omega

theorem projected_descendants_stay_right {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (ancestor start target : ℕ)
    (hproj : Projection rank owner tree)
    (hright : ancestor < start) (hrank : rank ancestor < rank start)
    (hpath : Relation.ReflTransGen (fun a b => (a,b) ∈ edges owner tree) start target) :
    ancestor < target ∧ rank ancestor < rank target := by
  induction hpath with
  | refl => exact ⟨hright,hrank⟩
  | @tail previous target hprefix hedge ih =>
      have hbetween := edge_min_between rank owner tree previous target hproj hedge
      have hstrict := (edge_strict_rank_and_bounds rank owner tree previous target hproj hedge).2.2.2.2
      constructor
      · by_contra hnot
        have hmin := hbetween.2.2 ancestor (by omega) (by omega)
        omega
      · omega

/-- A direct child and every one of its descendants stay on the same
key side of the parent. Thus the derived retained binary graph satisfies
search order, not merely a degree bound. -/
theorem projected_subtree_search_order {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (parent child descendant : ℕ)
    (hproj : Projection rank owner tree)
    (hedge : (parent,child) ∈ edges owner tree)
    (hpath : Relation.ReflTransGen (fun a b => (a,b) ∈ edges owner tree) child descendant) :
    (child < parent → descendant < parent) ∧
      (parent < child → parent < descendant) := by
  have hrank := (edge_strict_rank_and_bounds rank owner tree parent child hproj hedge).2.2.2.2
  constructor
  · intro hleft
    exact (projected_descendants_stay_left rank owner tree parent child descendant hproj hleft hrank hpath).1
  · intro hright
    exact (projected_descendants_stay_right rank owner tree parent child descendant hproj hright hrank hpath).1

theorem incoming_parent_unique {lo hi : ℕ} (rank owner : ℕ → ℕ)
    (tree : BST lo hi) (atom first second : ℕ)
    (hproj : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi)
    (hfirst : (first,atom) ∈ edges owner tree)
    (hsecond : (second,atom) ∈ edges owner tree) : first=second := by
  have hbalance := incoming_balance rank owner tree atom hproj hloc
  have hle : incoming owner tree atom ≤ 1 := by split_ifs at hbalance <;> omega
  let matchedEdges := (edges owner tree).filter (fun edge => edge.2 == atom)
  have hf : (first,atom) ∈ matchedEdges := by simp [matchedEdges,hfirst]
  have hs : (second,atom) ∈ matchedEdges := by simp [matchedEdges,hsecond]
  have hlen : matchedEdges.length=1 := by
    have hpos := List.length_pos_of_mem hf
    have heq : matchedEdges.length=incoming owner tree atom := by
      simp [matchedEdges,incoming,List.countP_eq_length_filter]
    omega
  obtain ⟨edge,hedge⟩ := List.length_eq_one_iff.mp hlen
  have hfe : (first,atom)=edge := by simpa [hedge] using hf
  have hse : (second,atom)=edge := by simpa [hedge] using hs
  exact congrArg Prod.fst (hfe.trans hse.symm)

#print axioms projection_of_cartesian
#print axioms outgoing_degree_le_four
#print axioms retained_binary_degree
#print axioms inactive_parent_exact
#print axioms incoming_balance
#print axioms projection_root_reaches
#print axioms projected_subtree_search_order
#print axioms incoming_parent_unique

end GreedyMerge.Fringe
