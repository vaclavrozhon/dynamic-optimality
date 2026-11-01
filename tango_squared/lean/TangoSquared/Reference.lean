import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
Concrete ordered trees partitioning an interval of natural-number labels.
The midpoint construction is the manuscript's secondary depth reference.
The uniqueness theorem is proved from the tree, rather than supplied as
an assumption about an abstract family of fragments.
-/

namespace TangoSquared

structure DepthSplit where
  lo : ℕ
  cut : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

def DepthSplit.Separates (s : DepthSplit) (e f : ℕ) : Prop :=
  s.lo ≤ e ∧ e ≤ s.cut ∧ s.cut < f ∧ f ≤ s.hi

inductive DepthTree : ℕ → ℕ → Type
  | leaf (a : ℕ) : DepthTree a a
  | node {a b : ℕ} (c : ℕ) (ha : a ≤ c) (hb : c < b)
      (left : DepthTree a c) (right : DepthTree (c + 1) b) : DepthTree a b

namespace DepthTree

def nodes : DepthTree a b → Finset DepthSplit
  | .leaf _ => ∅
  | @DepthTree.node a b c _ _ left right =>
      insert ⟨a, c, b⟩ (left.nodes ∪ right.nodes)

def locate : DepthTree a b → ℕ → ℕ → Option DepthSplit
  | .leaf _, _, _ => none
  | @DepthTree.node a b c _ _ left right, e, f =>
      if f ≤ c then left.locate e f
      else if c < e then right.locate e f
      else some ⟨a, c, b⟩

theorem node_bounds (t : DepthTree a b) {s : DepthSplit} (hs : s ∈ t.nodes) :
    a ≤ s.lo ∧ s.lo ≤ s.cut ∧ s.cut < s.hi ∧ s.hi ≤ b := by
  induction t with
  | leaf a => simp [nodes] at hs
  | @node a b c ha hb left right ihl ihr =>
      simp only [nodes, Finset.mem_insert, Finset.mem_union] at hs
      rcases hs with rfl | h | h
      · exact ⟨le_rfl, ha, hb, le_rfl⟩
      · obtain ⟨h₁, h₂, h₃, h₄⟩ := ihl h
        exact ⟨h₁, h₂, h₃, by omega⟩
      · obtain ⟨h₁, h₂, h₃, h₄⟩ := ihr h
        exact ⟨by omega, h₂, h₃, h₄⟩

theorem locate_of_separates (t : DepthTree a b) {s : DepthSplit}
    (hs : s ∈ t.nodes) (hsep : s.Separates e f) :
    t.locate e f = some s := by
  induction t with
  | leaf a => simp [nodes] at hs
  | @node a b c ha hb left right ihl ihr =>
      simp only [nodes, Finset.mem_insert, Finset.mem_union] at hs
      rcases hs with rfl | h | h
      · change a ≤ e ∧ e ≤ c ∧ c < f ∧ f ≤ b at hsep
        rcases hsep with ⟨he₀, he₁, hf₀, hf₁⟩
        simp [locate, show ¬ f ≤ c by omega, show ¬ c < e by omega]
      · have hbounds := left.node_bounds h
        have hf : f ≤ c := by rcases hsep with ⟨_, _, _, hf⟩; omega
        simp only [locate, if_pos hf]
        exact ihl h
      · have hbounds := right.node_bounds h
        have he : c < e := by rcases hsep with ⟨he, _, _, _⟩; omega
        have hf : ¬ f ≤ c := by rcases hsep with ⟨_, h₁, h₂, _⟩; omega
        simp only [locate, if_neg hf, if_pos he]
        exact ihr h

theorem exists_separating (t : DepthTree a b) (ha : a ≤ e)
    (hef : e < f) (hb : f ≤ b) :
    ∃ s, s ∈ t.nodes ∧ s.Separates e f := by
  induction t with
  | leaf a => omega
  | @node a b c hac hcb left right ihl ihr =>
      by_cases hf : f ≤ c
      · obtain ⟨s, hs, hsep⟩ := ihl ha hf
        exact ⟨s, by simp [nodes, hs], hsep⟩
      · by_cases he : c < e
        · obtain ⟨s, hs, hsep⟩ := ihr (by omega) hb
          exact ⟨s, by simp [nodes, hs], hsep⟩
        · refine ⟨⟨a,c,b⟩, by simp [nodes], ?_⟩
          change a ≤ e ∧ e ≤ c ∧ c < f ∧ f ≤ b
          exact ⟨ha, by omega, by omega, hb⟩

theorem unique_separating (t : DepthTree a b) (ha : a ≤ e)
    (hef : e < f) (hb : f ≤ b) :
    ∃! s, s ∈ t.nodes ∧ s.Separates e f := by
  obtain ⟨s, hs, hsep⟩ := t.exists_separating ha hef hb
  refine ⟨s, ⟨hs, hsep⟩, ?_⟩
  intro r hr
  have h₁ := t.locate_of_separates hs hsep
  have h₂ := t.locate_of_separates hr.1 hr.2
  exact Option.some.inj (h₂.symm.trans h₁)

def midpoint (a b : ℕ) (hab : a ≤ b) : DepthTree a b :=
  if h : a = b then h ▸ .leaf a
  else
    .node ((a + b) / 2) (by omega) (by omega)
      (midpoint a ((a + b) / 2) (by omega))
      (midpoint (((a + b) / 2) + 1) b (by omega))
termination_by b - a

theorem midpoint_unique_separating (H e f : ℕ) (hef : e < f) (hf : f ≤ H) :
    ∃! s, s ∈ (midpoint 0 H (Nat.zero_le H)).nodes ∧ s.Separates e f :=
  unique_separating _ (Nat.zero_le e) hef hf

end DepthTree
end TangoSquared
