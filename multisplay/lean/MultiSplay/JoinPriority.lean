import MultiSplay.JoinIntervals
import Splay.Lazy.CanonicalRankOrder
import Splay.Rank.TemporaryBoundarySnapshot

/-!
# Common joins in the doubled priorities used by the splay accounting

The existing article realization doubles all true comparison ranks to leave
room for temporary priorities. Doubling retains the canonical child order.
An old internal gap is still unchanged by a common join, whereas each former
root obtains raw gap two and contracted value three.
-/

namespace MultiSplay.JoinPriority

open Splay.Tree (BST)
open Splay.Rank (Snapshot External truePriority)
open Splay.Lazy (HeapView)
open Splay.Lazy.Canonical

variable {n : Nat}

theorem structure_eq (snapshot : Snapshot n) (tree : BST 0 n) :
    canonicalRoot snapshot.withTruePriority tree = canonicalRoot snapshot tree ∧
      canonicalParent snapshot.withTruePriority tree = canonicalParent snapshot tree ∧
      canonicalSide snapshot.withTruePriority tree = canonicalSide snapshot tree := by
  apply canonical_parent_side_eq_of_order snapshot snapshot.withTruePriority tree
  intro element owner parent
  have old := rank_canonicalParent_lt snapshot tree parent
  change 2 * snapshot.rank owner < 2 * snapshot.rank element
  omega

theorem attached_eq (snapshot : Snapshot n) (tree : BST 0 n) (assigned : List (External n))
    (owner : External n) (side : Splay.Lazy.Side) :
    (canonicalHeapView snapshot.withTruePriority tree).attachedTopDown assigned owner side =
      (canonicalHeapView snapshot tree).attachedTopDown assigned owner side := by
  have same := structure_eq snapshot tree
  simp only [HeapView.attachedTopDown, canonicalHeapView, same.2.1, same.2.2]

theorem rawGap_eq (snapshot : Snapshot n) (tree : BST 0 n) (element : External n) :
    (canonicalHeapView snapshot.withTruePriority tree).rawGap element =
      2 * (canonicalHeapView snapshot tree).rawGap element := by
  have same := structure_eq snapshot tree
  simp only [HeapView.rawGap, canonicalHeapView, same.2.1]
  cases parentEq : canonicalParent snapshot tree element with
  | none => simp
  | some owner => simp only [Splay.Rank.withTruePriority_rank, truePriority, Nat.cast_mul, Nat.cast_ofNat]; ring

theorem left_rawGap {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) {element : External l}
    (notRoot : element ≠ canonicalRoot (Snapshot.ofTree left).withTruePriority splayLeft) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority
      (JoinRanks.tree splayLeft splayRight)).rawGap (JoinIntervals.leftEmbedding l r element) =
      (canonicalHeapView (Snapshot.ofTree left).withTruePriority splayLeft).rawGap element := by
  rw [rawGap_eq, rawGap_eq, JoinHeap.left_rawGap left right splayLeft splayRight]
  simpa only [(structure_eq (Snapshot.ofTree left) splayLeft).1] using notRoot

theorem right_rawGap {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) {element : External r}
    (notRoot : element ≠ canonicalRoot (Snapshot.ofTree right).withTruePriority splayRight) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority
      (JoinRanks.tree splayLeft splayRight)).rawGap (JoinIntervals.rightEmbedding l r element) =
      (canonicalHeapView (Snapshot.ofTree right).withTruePriority splayRight).rawGap element := by
  rw [rawGap_eq, rawGap_eq, JoinHeap.right_rawGap left right splayLeft splayRight]
  simpa only [(structure_eq (Snapshot.ofTree right) splayRight).1] using notRoot

theorem left_root_rawGap {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority
      (JoinRanks.tree splayLeft splayRight)).rawGap
      (JoinIntervals.leftEmbedding l r (canonicalRoot (Snapshot.ofTree left).withTruePriority splayLeft)) = 2 := by
  rw [(structure_eq (Snapshot.ofTree left) splayLeft).1, rawGap_eq, JoinHeap.left_root_rawGap]
  decide

theorem right_root_rawGap {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) :
    (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority
      (JoinRanks.tree splayLeft splayRight)).rawGap
      (JoinIntervals.rightEmbedding l r (canonicalRoot (Snapshot.ofTree right).withTruePriority splayRight)) = 2 := by
  rw [(structure_eq (Snapshot.ofTree right) splayRight).1, rawGap_eq, JoinHeap.right_root_rawGap]
  decide

theorem left_structurallyValid {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r))
    (aRoot : canonicalRoot (Snapshot.ofTree left).withTruePriority splayLeft ∉ a)
    (bRoot : canonicalRoot (Snapshot.ofTree right).withTruePriority splayRight ∉ b)
    (source : Splay.Lazy.Block l)
    (valid : source.StructurallyValid (canonicalHeapView (Snapshot.ofTree left).withTruePriority splayLeft) a) :
    (BlockEmbedding.block (JoinIntervals.leftEmbedding l r) source).StructurallyValid
      (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree splayLeft splayRight))
      (JoinIntervals.assigned left right splayLeft splayRight a b) := by
  apply HeapEmbedding.structurallyValid _ _ _ a _ source valid
  · rw [attached_eq, attached_eq]
    exact JoinIntervals.left_children left right splayLeft splayRight a b
      (by simpa only [(structure_eq (Snapshot.ofTree left) splayLeft).1] using aRoot)
      (by simpa only [(structure_eq (Snapshot.ofTree right) splayRight).1] using bRoot) source.owner source.side
  · intro element member
    exact left_rawGap left right splayLeft splayRight (BlockEmbedding.member_ne_root _ source a valid member)

theorem right_structurallyValid {l r : Nat} (left : BST 0 l) (right : BST 0 r)
    (splayLeft : BST 0 l) (splayRight : BST 0 r) (a : List (External l)) (b : List (External r))
    (aRoot : canonicalRoot (Snapshot.ofTree left).withTruePriority splayLeft ∉ a)
    (bRoot : canonicalRoot (Snapshot.ofTree right).withTruePriority splayRight ∉ b)
    (source : Splay.Lazy.Block r)
    (valid : source.StructurallyValid (canonicalHeapView (Snapshot.ofTree right).withTruePriority splayRight) b) :
    (BlockEmbedding.block (JoinIntervals.rightEmbedding l r) source).StructurallyValid
      (canonicalHeapView (Snapshot.ofTree (JoinRanks.tree left right)).withTruePriority (JoinRanks.tree splayLeft splayRight))
      (JoinIntervals.assigned left right splayLeft splayRight a b) := by
  apply HeapEmbedding.structurallyValid _ _ _ b _ source valid
  · rw [attached_eq, attached_eq]
    exact JoinIntervals.right_children left right splayLeft splayRight a b
      (by simpa only [(structure_eq (Snapshot.ofTree left) splayLeft).1] using aRoot)
      (by simpa only [(structure_eq (Snapshot.ofTree right) splayRight).1] using bRoot) source.owner source.side
  · intro element member
    exact right_rawGap left right splayLeft splayRight (BlockEmbedding.member_ne_root _ source b valid member)

theorem root_contracted : Splay.Analysis.transientContractedGap 2 0 = 3 := by decide

end MultiSplay.JoinPriority
