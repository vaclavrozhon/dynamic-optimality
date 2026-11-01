import FringeProjection
import CutPath

/-!
Construct the actual retained-record binary tree of a canonical fringe.
An inactive separator is omitted; its winning adjacent gap is an extreme
root of one child tree, and the opposite tree is grafted to its empty side.
This construction will supply concrete cut trees for phase projections.
-/
namespace GreedyForest.ActiveTree

open Splay.Tree Splay.Tree.BST
open GreedyMerge.Fringe

inductive Sparse where
  | empty : Sparse
  | node (key : ℕ) (left right : Sparse) : Sparse
  deriving DecidableEq

namespace Sparse

def keys : Sparse → Finset ℕ
  | .empty => ∅
  | .node key left right => {key} ∪ left.keys ∪ right.keys

def edgeTo (parent : ℕ) : Sparse → Finset (ℕ × ℕ)
  | .empty => ∅
  | .node key _ _ => {(parent,key)}

def edges : Sparse → Finset (ℕ × ℕ)
  | .empty => ∅
  | .node key left right => left.edges ∪ right.edges ∪ left.edgeTo key ∪ right.edgeTo key

def Ordered : Sparse → Prop
  | .empty => True
  | .node key left right => Ordered left ∧ Ordered right ∧
      (∀ v ∈ left.keys, v < key) ∧ (∀ v ∈ right.keys, key < v)

def Heap (rank : ℕ → ℕ) : Sparse → Prop
  | .empty => True
  | .node key left right => Heap rank left ∧ Heap rank right ∧
      (∀ v ∈ left.keys, rank key ≤ rank v) ∧
      (∀ v ∈ right.keys, rank key ≤ rank v)

theorem root_mem (key : ℕ) (left right : Sparse) : key ∈ (node key left right).keys := by
  simp [keys]

theorem empty_of_keys_empty (tree : Sparse) (h : tree.keys = ∅) : tree = empty := by
  cases tree with
  | empty => rfl
  | node key left right =>
      have hm := root_mem key left right
      rw [h] at hm
      simp at hm

theorem right_empty_of_max {key : ℕ} {left right : Sparse}
    (ho : Ordered (.node key left right))
    (hm : ∀ v ∈ (Sparse.node key left right).keys, v ≤ key) : right = empty := by
  apply empty_of_keys_empty right
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hlt := ho.2.2.2 v hv
  have hle := hm v (by simp [keys,hv])
  omega

theorem left_empty_of_min {key : ℕ} {left right : Sparse}
    (ho : Ordered (.node key left right))
    (hm : ∀ v ∈ (Sparse.node key left right).keys, key ≤ v) : left = empty := by
  apply empty_of_keys_empty left
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hlt := ho.2.2.1 v hv
  have hle := hm v (by simp [keys,hv])
  omega

end Sparse

structure Rooted where
  key : ℕ
  left : Sparse
  right : Sparse

def Rooted.tree (root : Rooted) : Sparse := .node root.key root.left root.right

def active (owner : ℕ → ℕ) {lo hi : ℕ} : BST lo hi → Rooted
  | .empty i => ⟨2*i,.empty,.empty⟩
  | .node (root:=q) left right =>
      let a := active owner left
      let b := active owner right
      if owner q = 2*q then ⟨a.key,a.left,b.tree⟩
      else if owner q = 2*q+1 then ⟨2*q+1,a.tree,b.tree⟩
      else ⟨b.key,a.tree,b.right⟩

theorem active_root_eq {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (active owner tree).key = treeOwner owner tree := by
  induction tree with
  | empty => rfl
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hal := ihLeft hp.2.1 (by intro k hkl hku; exact hloc k hkl (by omega))
      have har := ihRight hp.2.2 (by intro k hkl hku; exact hloc k (by omega) hku)
      change (active owner (.node left right)).key = owner q
      rcases local_children_cases rank owner left right hp hloc with h | h | h
      · simp only [active,h.1,ite_true]
        exact hal.trans h.2.1
      · have hn : ¬ 2*q+1=2*q := by omega
        simp only [active,h.1,if_neg hn,ite_true]
      · have hn : ¬ 2*q+2=2*q := by omega
        have hn' : ¬ 2*q+2=2*q+1 := by omega
        simp only [active,h.1,if_neg hn,if_neg hn']
        exact har.trans h.2.1

theorem active_bounds {lo hi : ℕ} (owner : ℕ → ℕ) (tree : BST lo hi) :
    ∀ v ∈ (active owner tree).tree.keys, 2*lo ≤ v ∧ v ≤ 2*hi := by
  induction tree with
  | empty =>
      intro v hv
      simp [active,Rooted.tree,Sparse.keys] at hv
      subst v
      omega
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hlroot := ihLeft (active owner left).key
        (Sparse.root_mem _ _ _)
      have hrroot := ihRight (active owner right).key
        (Sparse.root_mem _ _ _)
      intro v hv
      simp only [active] at hv
      split_ifs at hv with hleft hvalue
      · simp only [Rooted.tree,Sparse.keys,Finset.mem_union,Finset.mem_singleton] at hv
        rcases hv with (hv | hv) | hv
        · subst v; omega
        · have hb := ihLeft v (by simp [Rooted.tree,Sparse.keys,hv])
          omega
        · have hb := ihRight v (by simpa [Rooted.tree,Sparse.keys,or_assoc] using hv)
          omega
      · simp only [Rooted.tree,Sparse.keys,Finset.mem_union,Finset.mem_singleton] at hv
        rcases hv with (hv | hv) | hv
        · subst v; omega
        · have hb := ihLeft v (by simpa [Rooted.tree,Sparse.keys,or_assoc] using hv)
          omega
        · have hb := ihRight v (by simpa [Rooted.tree,Sparse.keys,or_assoc] using hv)
          omega
      · simp only [Rooted.tree,Sparse.keys,Finset.mem_union,Finset.mem_singleton] at hv
        rcases hv with (hv | hv) | hv
        · subst v; omega
        · have hb := ihLeft v (by simpa [Rooted.tree,Sparse.keys,or_assoc] using hv)
          omega
        · have hb := ihRight v (by simp [Rooted.tree,Sparse.keys,hv])
          omega

theorem active_ordered {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    Sparse.Ordered (active owner tree).tree := by
  induction tree with
  | empty => simp [active,Rooted.tree,Sparse.Ordered,Sparse.keys]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hll : LocalOwners rank owner lo q := by
        intro k hkl hku; exact hloc k hkl (by omega)
      have hrr : LocalOwners rank owner (q+1) hi := by
        intro k hkl hku; exact hloc k (by omega) hku
      have hal := ihLeft hp.2.1 hll
      have har := ihRight hp.2.2 hrr
      have hlroot := active_root_eq rank owner left hp.2.1 hll
      have hrroot := active_root_eq rank owner right hp.2.2 hrr
      rcases local_children_cases rank owner left right hp hloc with h | h | h
      · simp only [active,h.1,ite_true,Rooted.tree,Sparse.Ordered]
        refine ⟨hal.1,har,hal.2.2.1,?_⟩
        intro v hv
        have hb := active_bounds owner right v hv
        omega
      · have hn : ¬ 2*q+1=2*q := by omega
        simp only [active,h.1,if_neg hn,ite_true,Rooted.tree,Sparse.Ordered]
        refine ⟨hal,har,?_,?_⟩
        · intro v hv
          have hb := active_bounds owner left v hv
          omega
        · intro v hv
          have hb := active_bounds owner right v hv
          omega
      · have hn : ¬ 2*q+2=2*q := by omega
        have hn' : ¬ 2*q+2=2*q+1 := by omega
        simp only [active,h.1,if_neg hn,if_neg hn',Rooted.tree,Sparse.Ordered]
        refine ⟨hal,har.2.1,?_,har.2.2.2⟩
        intro v hv
        have hb := active_bounds owner left v hv
        omega

theorem active_heap {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    Sparse.Heap rank (active owner tree).tree := by
  induction tree with
  | empty => simp [active,Rooted.tree,Sparse.Heap,Sparse.keys]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hll : LocalOwners rank owner lo q := by
        intro k hkl hku; exact hloc k hkl (by omega)
      have hrr : LocalOwners rank owner (q+1) hi := by
        intro k hkl hku; exact hloc k (by omega) hku
      have hal := ihLeft hp.2.1 hll
      have har := ihRight hp.2.2 hrr
      have hlroot := active_root_eq rank owner left hp.2.1 hll
      have hrroot := active_root_eq rank owner right hp.2.2 hrr
      have hmin : ∀ v, 2*lo ≤ v → v ≤ 2*hi → rank (owner q) ≤ rank v := hp.1.1.2.2
      rcases local_children_cases rank owner left right hp hloc with h | h | h
      · simp only [active,h.1,ite_true,Rooted.tree,Sparse.Heap]
        refine ⟨hal.1,har,hal.2.2.1,?_⟩
        intro v hv
        have hb := active_bounds owner right v hv
        have he : (active owner left).key = owner q := by omega
        rw [he]
        exact hmin v (by omega) hb.2
      · have hn : ¬ 2*q+1=2*q := by omega
        simp only [active,h.1,if_neg hn,ite_true,Rooted.tree,Sparse.Heap]
        refine ⟨hal,har,?_,?_⟩
        · intro v hv
          have hb := active_bounds owner left v hv
          rw [← h.1]
          exact hmin v hb.1 (by omega)
        · intro v hv
          have hb := active_bounds owner right v hv
          rw [← h.1]
          exact hmin v (by omega) hb.2
      · have hn : ¬ 2*q+2=2*q := by omega
        have hn' : ¬ 2*q+2=2*q+1 := by omega
        simp only [active,h.1,if_neg hn,if_neg hn',Rooted.tree,Sparse.Heap]
        refine ⟨hal,har.2.1,?_,har.2.2.2⟩
        intro v hv
        have hb := active_bounds owner left v hv
        have he : (active owner right).key = owner q := by omega
        rw [he]
        exact hmin v hb.1 (by omega)

theorem graft_right_edges (a b : Rooted) (ha : a.right = .empty) :
    (Sparse.node a.key a.left b.tree).edges =
      a.tree.edges ∪ b.tree.edges ∪ {(a.key,b.key)} := by
  ext edge
  simp [Rooted.tree,Sparse.edges,Sparse.edgeTo,ha]
  tauto

theorem graft_left_edges (a b : Rooted) (hb : b.left = .empty) :
    (Sparse.node b.key a.tree b.right).edges =
      a.tree.edges ∪ b.tree.edges ∪ {(b.key,a.key)} := by
  ext edge
  simp [Rooted.tree,Sparse.edges,Sparse.edgeTo,hb]

theorem join_root_edges (key : ℕ) (a b : Rooted) :
    (Sparse.node key a.tree b.tree).edges =
      a.tree.edges ∪ b.tree.edges ∪ {(key,a.key),(key,b.key)} := by
  ext edge
  simp [Rooted.tree,Sparse.edges,Sparse.edgeTo]

def retainedEdges (owner : ℕ → ℕ) {lo hi : ℕ} (tree : BST lo hi) : Finset (ℕ × ℕ) :=
  (GreedyMerge.Fringe.edges owner tree).toFinset.filter (fun e => Retained owner e.2)

theorem retainedEdges_node {lo q hi : ℕ} (owner : ℕ → ℕ)
    (left : BST lo q) (right : BST (q+1) hi) :
    retainedEdges owner (.node left right) =
      retainedEdges owner left ∪ retainedEdges owner right ∪
        ((localChildren owner left right).map (fun c => (owner q,c))).toFinset.filter
          (fun e => Retained owner e.2) := by
  simp [retainedEdges,GreedyMerge.Fringe.edges,List.toFinset_append,Finset.filter_union]

/-- The constructed sparse tree contains exactly the retained-child
edges of the literal ternary contraction. No Cartesian skeleton is an
input to this theorem. -/
theorem active_edges {lo hi : ℕ} (rank owner : ℕ → ℕ) (tree : BST lo hi)
    (hp : Projection rank owner tree) (hloc : LocalOwners rank owner lo hi) :
    (active owner tree).tree.edges = retainedEdges owner tree := by
  induction tree with
  | empty => simp [active,Rooted.tree,Sparse.edges,Sparse.edgeTo,retainedEdges,GreedyMerge.Fringe.edges]
  | @node lo q hi left right ihLeft ihRight =>
      have hl := left.lower_le_upper
      have hr := right.lower_le_upper
      have hll : LocalOwners rank owner lo q := by
        intro k hkl hku; exact hloc k hkl (by omega)
      have hrr : LocalOwners rank owner (q+1) hi := by
        intro k hkl hku; exact hloc k (by omega) hku
      have hal := ihLeft hp.2.1 hll
      have har := ihRight hp.2.2 hrr
      have hlroot := active_root_eq rank owner left hp.2.1 hll
      have hrroot := active_root_eq rank owner right hp.2.2 hrr
      have hol := active_ordered rank owner left hp.2.1 hll
      have hor := active_ordered rank owner right hp.2.2 hrr
      have hrl := treeOwner_retained left hll
      have hrrt := treeOwner_retained right hrr
      rw [retainedEdges_node]
      rcases local_children_cases rank owner left right hp hloc with h | h | h
      · have hempty : (active owner left).right = .empty := by
          apply Sparse.right_empty_of_max hol
          intro v hv
          have hb := active_bounds owner left v hv
          omega
        have hd : (active owner (.node left right)).tree =
            Sparse.node (active owner left).key (active owner left).left (active owner right).tree := by
          simp only [active,h.1,ite_true,Rooted.tree]
        rw [hd,graft_right_edges _ _ hempty,hal,har,hlroot,hrroot]
        have hinactive : ¬ Retained owner (2*q+1) := by simp [h.1]
        simp [h.2.2,h.1,h.2.1,hinactive,hrrt,Finset.filter_insert,Finset.filter_singleton,Finset.union_assoc]
      · have hn : ¬ 2*q+1=2*q := by omega
        have hd : (active owner (.node left right)).tree =
            Sparse.node (2*q+1) (active owner left).tree (active owner right).tree := by
          simp only [active,h.1,if_neg hn,ite_true,Rooted.tree]
        rw [hd,join_root_edges,hal,har,hlroot,hrroot]
        simp [h.2,h.1,hrl,hrrt,Finset.union_assoc,Finset.filter_insert,Finset.filter_singleton]
      · have hempty : (active owner right).left = .empty := by
          apply Sparse.left_empty_of_min hor
          intro v hv
          have hb := active_bounds owner right v hv
          omega
        have hn : ¬ 2*q+2=2*q := by omega
        have hn' : ¬ 2*q+2=2*q+1 := by omega
        have hd : (active owner (.node left right)).tree =
            Sparse.node (active owner right).key (active owner left).tree (active owner right).right := by
          simp only [active,h.1,if_neg hn,if_neg hn',Rooted.tree]
        rw [hd,graft_left_edges _ _ hempty,hal,har,hlroot,hrroot]
        have hinactive : ¬ Retained owner (2*q+1) := by simp [h.1]
        simp [h.2.2,h.1,h.2.1,hinactive,hrl,Finset.filter_insert,Finset.filter_singleton,Finset.union_assoc]

end GreedyForest.ActiveTree
