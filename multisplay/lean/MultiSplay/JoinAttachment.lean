import MultiSplay.JoinComponentGeometry
import Splay.Accounting.CanonicalCrossSideUnbroken

/-!
# Full attachment order through common joins and splits

In addition to the side-restricted child lists, every old light edge retains
its branch and has its attachment depth increased by exactly one. This keeps
the full order used by the article's unbroken-block invariant.
-/

namespace MultiSplay.JoinAttachment

open Splay.Tree (BST)
open Splay.Rank (Snapshot External)
open Splay.Lazy.Canonical
open Splay.Accounting

variable {n m l r : Nat}

theorem priority_edges (snapshot : Snapshot n) (tree : Splay.Tree.BST 0 n) :
    fullEdges snapshot.withTruePriority tree = fullEdges snapshot tree := by
  apply treeEdges_eq_of_edge_order snapshot snapshot.withTruePriority tree (Nat.le_refl n) 0
  intro edge member
  have ordered := mem_treeEdges_rank_lt snapshot tree (Nat.le_refl n) member
  change 2 * snapshot.rank edge.owner < 2 * snapshot.rank edge.child
  omega

theorem priority_incoming (snapshot : Snapshot n) (tree : Splay.Tree.BST 0 n) (x : External n) :
    incomingEdge? snapshot.withTruePriority tree x = incomingEdge? snapshot tree x := by
  cases lookup : incomingEdge? snapshot tree x with
  | none =>
      rw [incomingEdge?_eq_none_iff] at lookup ⊢
      rw [(JoinPriority.structure_eq snapshot tree).1]
      exact lookup
  | some edge =>
      obtain ⟨member, child⟩ := incomingEdge?_some_mem snapshot tree lookup
      have mapped : edge ∈ fullEdges snapshot.withTruePriority tree := by rw [priority_edges]; exact member
      simpa only [child] using JoinHeap.incoming_of_member snapshot.withTruePriority tree mapped

theorem left_incoming (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r) (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
    {x : External l} {edge : Edge l}
    (found : incomingEdge? (Snapshot.ofTree left).withTruePriority sl x = some edge) :
    incomingEdge? (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)
      (JoinIntervals.leftEmbedding l r x) = some (RankEmbedding.edge 0 1 (by omega) edge) := by
  rw [priority_incoming] at found ⊢
  exact JoinHeap.left_incoming left right sl sr found

theorem right_incoming (left : Splay.Tree.BST 0 l) (right : Splay.Tree.BST 0 r) (sl : Splay.Tree.BST 0 l) (sr : Splay.Tree.BST 0 r)
    {x : External r} {edge : Edge r}
    (found : incomingEdge? (Snapshot.ofTree right).withTruePriority sr x = some edge) :
    incomingEdge? (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree sl sr)
      (JoinIntervals.rightEmbedding l r x) = some (RankEmbedding.edge (0+l+1) 1 (by omega) edge) := by
  rw [priority_incoming] at found ⊢
  exact JoinHeap.right_incoming left right sl sr found

theorem edge_above_iff (offset depth : Nat) (fits : offset+n ≤ m) (first second : Edge n) :
    edgeStrictlyAbove (RankEmbedding.edge offset depth fits first) (RankEmbedding.edge offset depth fits second) ↔
      edgeStrictlyAbove first second := by
  simp only [edgeStrictlyAbove, RankEmbedding.edge, Nat.add_lt_add_iff_left, Nat.add_left_cancel_iff]

theorem above_iff (offset depth : Nat) (fits : offset+n ≤ m)
    (before : Snapshot n) (after : Snapshot m) (small : Splay.Tree.BST 0 n) (big : Splay.Tree.BST 0 m)
    (edges : ∀ x edge, incomingEdge? before small x = some edge →
      incomingEdge? after big (RankEmbedding.external offset fits x) = some (RankEmbedding.edge offset depth fits edge))
    (x y : External n) (xRoot : x ≠ canonicalRoot before small) (yRoot : y ≠ canonicalRoot before small) :
    ChildStrictlyAbove after big (RankEmbedding.external offset fits x) (RankEmbedding.external offset fits y) ↔
      ChildStrictlyAbove before small x y := by
  obtain ⟨first, firstFound, _, _⟩ := exists_incomingEdge?_eq_some_of_ne_root before small xRoot
  obtain ⟨second, secondFound, _, _⟩ := exists_incomingEdge?_eq_some_of_ne_root before small yRoot
  simp [ChildStrictlyAbove, edges _ _ firstFound, edges _ _ secondFound, firstFound, secondFound,
    edge_above_iff]

theorem between_iff (offset depth : Nat) (fits : offset+n ≤ m)
    (before : Snapshot n) (after : Snapshot m) (small : Splay.Tree.BST 0 n) (big : Splay.Tree.BST 0 m)
    (edges : ∀ x edge, incomingEdge? before small x = some edge →
      incomingEdge? after big (RankEmbedding.external offset fits x) = some (RankEmbedding.edge offset depth fits edge))
    (x y z : External n) (xRoot : x ≠ canonicalRoot before small) (yRoot : y ≠ canonicalRoot before small)
    (zRoot : z ≠ canonicalRoot before small) :
    ChildBetween after big (RankEmbedding.external offset fits x) (RankEmbedding.external offset fits y) (RankEmbedding.external offset fits z) ↔
      ChildBetween before small x y z := by
  simp only [ChildBetween, above_iff offset depth fits before after small big edges x y xRoot yRoot,
    above_iff offset depth fits before after small big edges y z yRoot zRoot,
    above_iff offset depth fits before after small big edges z y zRoot yRoot,
    above_iff offset depth fits before after small big edges y x yRoot xRoot]

end MultiSplay.JoinAttachment
