import Splay.Assumptions.NormalForm
import Splay.Rank.FromTree
import Splay.Rank.Heavy
import Splay.Rank.HeapOrder

namespace Splay.Assumptions.NormalForm

/--
The explicit additive depth bound that the later splay argument actually
consumes from riblessness.

For every value key, the two adjacent external null positions are at most
`slack` levels deeper.  Stating this extensional consequence directly avoids
silently identifying the current `IsNormal` fields (height and rotation
depth) with riblessness: neither of those fields implies this property.
-/
def HasRelevantNeighborDepthBound {n : ℕ}
    (tree : ComparisonTree n) (slack : ℕ) : Prop :=
  ∀ key : Fin n,
    tree.externalDepth (Rank.leftNullPos key).val ≤
        tree.depth key.val + slack ∧
      tree.externalDepth (Rank.rightNullPos key).val ≤
        tree.depth key.val + slack

/--
The rank-level form needed for the low-rank neighbors of an accessed value.
It is kept distinct from the depth formulation so the bridge through
`Snapshot.ofTree` is a theorem, not a definitional assumption.
-/
def HasRelevantNeighborRankBound {n : ℕ}
    (snapshot : Rank.Snapshot n) (slack : ℕ) : Prop :=
  ∀ key : Fin n,
    snapshot.rank (Rank.leftNullPos key) ≤
        snapshot.rank (Rank.valuePos key) + slack ∧
      snapshot.rank (Rank.rightNullPos key) ≤
        snapshot.rank (Rank.valuePos key) + slack

/--
At a value position, external depth agrees with ordinary search depth.
This is the elementary tree fact that connects the paper's value ranks to
the depth language used by normal form.
-/
theorem externalDepth_value_eq_depth
    {lower upper key : ℕ} (tree : Tree.BST lower upper)
    (insideLower : lower ≤ key) (insideUpper : key < upper) :
    tree.externalDepth (2 * key + 1) = tree.depth key := by
  induction tree with
  | empty boundary =>
      omega
  | @node lower root upper left right ihLeft ihRight =>
      by_cases atRoot : key = root
      · subst key
        rw [Tree.BST.externalDepth_root, Tree.BST.depth_root]
      · by_cases inLeft : key < root
        · rw [Tree.BST.externalDepth_node_of_lt_root
              left right (by omega)]
          rw [Tree.BST.depth_node_of_lt_root left right inLeft]
          rw [ihLeft insideLower inLeft]
        · have inRight : root < key := by omega
          rw [Tree.BST.externalDepth_node_of_root_lt
              left right (by omega)]
          rw [Tree.BST.depth_node_of_root_lt left right inRight]
          rw [ihRight (by omega) insideUpper]

/-- `Snapshot.ofTree` assigns a value position its ordinary tree depth. -/
@[simp]
theorem ofTree_rank_valuePos_eq_depth {n : ℕ}
    (tree : ComparisonTree n) (key : Fin n) :
    (Rank.Snapshot.ofTree tree).rank (Rank.valuePos key) =
      tree.depth key.val := by
  change
    tree.externalDepth (2 * key.val + 1) = tree.depth key.val
  exact externalDepth_value_eq_depth tree (by omega) key.isLt

/-- A key certified as the root has ordinary depth zero. -/
theorem depth_eq_zero_of_hasRoot {lower upper key : ℕ}
    {tree : Tree.BST lower upper} (root : tree.HasRoot key) :
    tree.depth key = 0 := by
  obtain ⟨left, right, rfl⟩ := root
  exact Tree.BST.depth_root left right

/--
An explicit adjacent-null depth bound becomes the corresponding rank bound in
the snapshot induced by the same tree.
-/
theorem HasRelevantNeighborDepthBound.toRankBound
    {n slack : ℕ} {tree : ComparisonTree n}
    (bound : HasRelevantNeighborDepthBound tree slack) :
    HasRelevantNeighborRankBound (Rank.Snapshot.ofTree tree) slack := by
  intro key
  have depthBound := bound key
  constructor
  · change
      tree.externalDepth (2 * key.val) ≤
        tree.externalDepth (2 * key.val + 1) + slack
    rw [externalDepth_value_eq_depth tree (by omega) key.isLt]
    exact depthBound.1
  · change
      tree.externalDepth (2 * key.val + 2) ≤
        tree.externalDepth (2 * key.val + 1) + slack
    rw [externalDepth_value_eq_depth tree (by omega) key.isLt]
    exact depthBound.2

namespace HasRelevantNeighborDepthBound

/-- The left adjacent null of a root key has absolute rank at most `slack`. -/
theorem leftNull_rank_le_of_hasRoot
    {n slack : ℕ} {tree : ComparisonTree n}
    (bound : HasRelevantNeighborDepthBound tree slack)
    (key : Fin n) (root : tree.HasRoot key.val) :
    (Rank.Snapshot.ofTree tree).rank (Rank.leftNullPos key) ≤ slack := by
  have relative := (bound.toRankBound key).1
  rw [ofTree_rank_valuePos_eq_depth,
    depth_eq_zero_of_hasRoot root] at relative
  simpa using relative

/-- The right adjacent null of a root key has absolute rank at most `slack`. -/
theorem rightNull_rank_le_of_hasRoot
    {n slack : ℕ} {tree : ComparisonTree n}
    (bound : HasRelevantNeighborDepthBound tree slack)
    (key : Fin n) (root : tree.HasRoot key.val) :
    (Rank.Snapshot.ofTree tree).rank (Rank.rightNullPos key) ≤ slack := by
  have relative := (bound.toRankBound key).2
  rw [ofTree_rank_valuePos_eq_depth,
    depth_eq_zero_of_hasRoot root] at relative
  simpa using relative

end HasRelevantNeighborDepthBound

/--
A low-rank path has only a bounded number of heap ancestors.  This is the
checked numerical step used when low neighbor ranks are converted into a
constant number of possible junction participants.
-/
theorem heapAncestorChain_length_le_of_rank_le
    {α : Type*} {rank : α → ℕ} {path : α} {ancestors : List α}
    {bound : ℕ} (pathRank : rank path ≤ bound)
    (chain : Rank.IsHeapAncestorChain rank (path :: ancestors)) :
    (path :: ancestors).length ≤ bound + 1 := by
  calc
    (path :: ancestors).length ≤ rank path + 1 :=
      Rank.heapAncestorChain_length_le_rank_succ
        rank path ancestors chain
    _ ≤ bound + 1 := Nat.add_le_add_right pathRank 1

/--
An interval minimum containing a low-rank external position is itself
low-rank.  This isolates the exact implication used for the paper's
`x⁻`/`x⁺` vertices.
-/
theorem intervalMin_rank_le_of_contains
    {n bound : ℕ} (snapshot : Rank.Snapshot n)
    {lower upper witness : Rank.External n}
    (nonempty : lower ≤ upper)
    (contains : lower ≤ witness ∧ witness ≤ upper)
    (witnessRank : snapshot.rank witness ≤ bound) :
    snapshot.rank (snapshot.intervalMin lower upper nonempty) ≤ bound := by
  have minimum :=
    snapshot.intervalMin_isMin lower upper nonempty
  exact
    (minimum.2.2 witness contains.1 contains.2).trans witnessRank

/--
Consequently, the heap-ancestor chain above such an interval minimum has
length at most `bound + 1`.
-/
theorem intervalMin_heapAncestorChain_length_le
    {n bound : ℕ} (snapshot : Rank.Snapshot n)
    {lower upper witness : Rank.External n}
    (nonempty : lower ≤ upper)
    (contains : lower ≤ witness ∧ witness ≤ upper)
    (witnessRank : snapshot.rank witness ≤ bound)
    (ancestors : List (Rank.External n))
    (chain :
      Rank.IsHeapAncestorChain snapshot.rank
        (snapshot.intervalMin lower upper nonempty :: ancestors)) :
    (snapshot.intervalMin lower upper nonempty :: ancestors).length ≤
      bound + 1 := by
  apply heapAncestorChain_length_le_of_rank_le
    (intervalMin_rank_le_of_contains snapshot nonempty
      contains witnessRank)
    chain

/--
Normal-form constants strengthened by the one additional universal constant
needed for relevant neighboring external positions.
-/
structure StructuralBounds extends Bounds where
  neighborDepthSlack : ℕ

/--
The strengthened structural trace invariant.

This deliberately contains the old `IsNormal` proof as a field and adds the
missing adjacent-null depth property at every state.  No theorem below claims
that `IsNormal` alone implies this structure.
-/
structure IsStructurallyNormal
    {n : ℕ} {accesses : List (Fin n)}
    (bounds : StructuralBounds)
    (trace : ComparisonTrace n accesses) : Prop where
  normal : IsNormal bounds.toBounds trace
  relevantNeighborDepth_le :
    ∀ time,
      HasRelevantNeighborDepthBound
        (trace.state time) bounds.neighborDepthSlack

namespace IsStructurallyNormal

theorem height_le
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace) (time) :
    (trace.state time).height ≤
      bounds.heightMultiplier * Analysis.stabilizedLog n :=
  normal.normal.height_le time

theorem rotationDepth_le
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace) (step) :
    trace.rotationDepth step ≤ bounds.maxRotationDepth :=
  normal.normal.rotationDepth_le step

/-- Every state exports the exact rank-level neighbor invariant. -/
theorem state_neighborRankBound
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace) (time) :
    HasRelevantNeighborRankBound
      (Rank.Snapshot.ofTree (trace.state time))
      bounds.neighborDepthSlack :=
  (normal.relevantNeighborDepth_le time).toRankBound

/-- At a served request, the left adjacent null has uniformly bounded rank. -/
theorem served_leftNull_rank_le
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (request : Fin accesses.length) :
    let key := accesses.get request
    (Rank.Snapshot.ofTree
        (trace.state (trace.servedAt request))).rank
          (Rank.leftNullPos key) ≤ bounds.neighborDepthSlack := by
  dsimp only
  exact
    HasRelevantNeighborDepthBound.leftNull_rank_le_of_hasRoot
      (normal.relevantNeighborDepth_le (trace.servedAt request))
      (accesses.get request) (trace.serves request)

/-- At a served request, the right adjacent null has uniformly bounded rank. -/
theorem served_rightNull_rank_le
    {n : ℕ} {accesses : List (Fin n)}
    {bounds : StructuralBounds}
    {trace : ComparisonTrace n accesses}
    (normal : IsStructurallyNormal bounds trace)
    (request : Fin accesses.length) :
    let key := accesses.get request
    (Rank.Snapshot.ofTree
        (trace.state (trace.servedAt request))).rank
          (Rank.rightNullPos key) ≤ bounds.neighborDepthSlack := by
  dsimp only
  exact
    HasRelevantNeighborDepthBound.rightNull_rank_le_of_hasRoot
      (normal.relevantNeighborDepth_le (trace.servedAt request))
      (accesses.get request) (trace.serves request)

end IsStructurallyNormal

/--
The honest strengthened normal-form hypothesis.

It is intentionally a separate proposition: the existing `Hypothesis` does
not contain riblessness or its relevant-neighbor consequence, so there is no
converse theorem from `Hypothesis` to `StructuralHypothesis`.
-/
def StructuralHypothesis (model : CostModel) : Prop :=
  ∃ bounds : StructuralBounds,
    ∀ (n : ℕ), 0 < n →
      ∀ accesses : List (Fin n),
        ∃ trace : ComparisonTrace n accesses,
          IsStructurallyNormal bounds trace ∧
            trace.cost ≤
              bounds.costMultiplier * model.optCost accesses

/-- Forgetting the added structural field recovers the original hypothesis. -/
theorem StructuralHypothesis.toHypothesis {model : CostModel}
    (hypothesis : StructuralHypothesis model) :
    Hypothesis model := by
  obtain ⟨bounds, realizes⟩ := hypothesis
  refine ⟨bounds.toBounds, ?_⟩
  intro n positive accesses
  obtain ⟨trace, structural, cost⟩ :=
    realizes n positive accesses
  exact ⟨trace, structural.normal, cost⟩

end Splay.Assumptions.NormalForm
