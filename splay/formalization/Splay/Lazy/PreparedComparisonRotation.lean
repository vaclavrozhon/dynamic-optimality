import Splay.Lazy.RotationTrace
import Splay.Lazy.SelectedHeapView
import Splay.Lazy.SplayTrace
import Splay.Lazy.StableRankUpdate

namespace Splay.Lazy

open Splay.Rank

/--
The exact reduction certificate left to the junction/split preparation
algorithm for one local comparison-tree rotation.

The prefix has already installed the heavy-path structure selected by the
post-rotation comparison snapshot, while retaining the pre-rotation numeric
ranks.  It ends at `RankPrepared`, and its blocks are aligned with one exact
unit-valued rank-shift witness for the given rotation.  This structure states
the finite prefix obligation explicitly; no inhabitant is postulated here.
-/
structure PreparedComparisonRotation {n : ℕ}
    (params : Interface.Parameters) (splayTree : Tree.BST 0 n)
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    (initial : State n) where
  rotation :
    Tree.BST.RotationAt rotationDepth
      beforeComparison afterComparison
  initial_represents :
    initial.Represents params
      (Snapshot.ofTree beforeComparison) splayTree
  elementShiftAt : ℕ → ℤ
  exactUpdate :
    ExactTreeRankUpdate
      beforeComparison afterComparison elementShiftAt
  unitShift : IsUnitRotationShift elementShiftAt
  blockShift : Block n → ℤ
  prepared : State n
  prefixEvents : List (Event n)
  prefixTrace :
    Trace params initial prefixEvents prepared
  rankPrepared : prepared.RankPrepared params
  view_eq :
    prepared.view =
      Canonical.canonicalHeapViewWithRank
        (Snapshot.ofTree afterComparison)
        (Snapshot.ofTree beforeComparison).rank
        splayTree
  blocksAligned :
    prepared.BlocksAlignedWithShift
      (fun element => elementShiftAt element.val) blockShift

/--
The remaining local algorithmic obligation: construct the explicit prepared
prefix certificate for every represented input and contextual comparison
rotation.

This is only a predicate describing the required constructor.  The module
proves that satisfying it is sufficient; it does not assume or assert that a
preparer exists.
-/
def ComparisonRotationPreparer {n : ℕ}
    (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeComparison afterComparison : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison →
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree →
        Nonempty
          (PreparedComparisonRotation
            params splayTree
            (rotationDepth := rotationDepth)
            (beforeComparison := beforeComparison)
            (afterComparison := afterComparison)
            initial)

namespace PreparedComparisonRotation

/--
The mixed prepared view and the canonical post-rotation view have identical
heap structure; they differ only in their numeric rank function.
-/
theorem sameStructure_afterView {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) :
    certificate.prepared.view.SameStructure
      (Canonical.canonicalHeapViewWithRank
        (Snapshot.ofTree afterComparison)
        (Snapshot.ofTree afterComparison).rank
        splayTree) := by
  rw [certificate.view_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The prepared mixed view still carries the pre-rotation numeric ranks. -/
theorem beforeRanks {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) :
    certificate.prepared.view.rank =
      (Snapshot.ofTree beforeComparison).rank := by
  rw [certificate.view_eq]
  exact Canonical.canonicalHeapViewWithRank_rank
    (Snapshot.ofTree afterComparison)
    (Snapshot.ofTree beforeComparison).rank
    splayTree

/-- The target view carries exactly the post-rotation numeric ranks. -/
theorem afterRanks {n : ℕ}
    {splayTree : Tree.BST 0 n}
    (afterComparison : Tree.BST 0 n) :
    (Canonical.canonicalHeapViewWithRank
        (Snapshot.ofTree afterComparison)
        (Snapshot.ofTree afterComparison).rank
        splayTree).rank =
      (Snapshot.ofTree afterComparison).rank :=
  Canonical.canonicalHeapViewWithRank_rank
    (Snapshot.ofTree afterComparison)
    (Snapshot.ofTree afterComparison).rank
    splayTree

/--
The exact tree-rank equation and block alignment assemble the concrete
blockwise-uniform rank update consumed by `RankUpdateCompatible`.
-/
theorem blockwiseUniform {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) :
    State.BlockwiseUniformRankShift
      certificate.prepared
      (Canonical.canonicalHeapViewWithRank
        (Snapshot.ofTree afterComparison)
        (Snapshot.ofTree afterComparison).rank
        splayTree)
      (fun element => certificate.elementShiftAt element.val)
      certificate.blockShift := by
  refine {
    sameStructure := certificate.sameStructure_afterView
    rankShift := ?_
    growing := certificate.blocksAligned.growing
    shrinking_empty := certificate.blocksAligned.shrinking_empty
    shrinking_nonempty := certificate.blocksAligned.shrinking_nonempty
  }
  intro element
  exact certificate.exactUpdate.heapViewRankShift
    certificate.beforeRanks
    (afterRanks afterComparison)
    element

/-- The prepared blockwise update satisfies the primitive compatibility API. -/
theorem compatible {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) :
    certificate.prepared.RankUpdateCompatible
      (Canonical.canonicalHeapViewWithRank
        (Snapshot.ofTree afterComparison)
        (Snapshot.ofTree afterComparison).rank
        splayTree)
      certificate.blockShift :=
  certificate.blockwiseUniform.compatible
    certificate.rankPrepared.valid

/-- The true post-rotation canonical view is heap ordered. -/
theorem afterView_heapOrdered {n : ℕ}
    {splayTree : Tree.BST 0 n}
    (afterComparison : Tree.BST 0 n) :
    (Canonical.canonicalHeapViewWithRank
      (Snapshot.ofTree afterComparison)
      (Snapshot.ofTree afterComparison).rank
      splayTree).HeapOrdered := by
  rw [Canonical.canonicalHeapViewWithRank_trueRank]
  exact Canonical.canonicalHeapView_heapOrdered
    (Snapshot.ofTree afterComparison) splayTree

/--
Discharge the rank-update suffix of a prepared certificate.  The prefix is
extended by exactly one silent event, and the endpoint represents the
canonical post-rotation comparison snapshot.
-/
theorem existsRepresentedTransition {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) :
    Nonempty
      (RepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree
        initial) := by
  let afterView :=
    Canonical.canonicalHeapViewWithRank
      (Snapshot.ofTree afterComparison)
      (Snapshot.ofTree afterComparison).rank
      splayTree
  let final :=
    certificate.prepared.absorbRankUpdate
      afterView certificate.blockShift
  have suffix :=
    certificate.rankPrepared.absorbRankUpdate_trace_stable
      certificate.compatible
      (afterView_heapOrdered afterComparison)
  refine ⟨{
    initial_represents := certificate.initial_represents
    final := final
    events := certificate.prefixEvents ++ [.silent]
    trace :=
      RepresentedTransition.trace_append
        certificate.prefixTrace suffix.1
    final_represents := ?_
  }⟩
  refine {
    stable := suffix.2
    view_eq := ?_
  }
  change afterView =
    Canonical.canonicalHeapView
      (Snapshot.ofTree afterComparison) splayTree
  exact Canonical.canonicalHeapViewWithRank_trueRank
    (Snapshot.ofTree afterComparison) splayTree

end PreparedComparisonRotation

/--
The complete no-junction case.

If the represented pre-rotation state already has the structural view selected
by the post-rotation snapshot (while still carrying the old ranks), and its
blocks align with whichever exact unit shift the rotation exports, the
preparation prefix is empty.  The rotation is then realized by the single
silent rank-update suffix proved above.
-/
theorem existsRepresentedTransition_of_aligned_noJunction {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    {rotationDepth : ℕ}
    {beforeComparison afterComparison : Tree.BST 0 n}
    (rotation :
      Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree)
    (viewAlreadyPrepared :
      initial.view =
        Canonical.canonicalHeapViewWithRank
          (Snapshot.ofTree afterComparison)
          (Snapshot.ofTree beforeComparison).rank
          splayTree)
    (alignment :
      ∀ elementShiftAt : ℕ → ℤ,
        ExactTreeRankUpdate
            beforeComparison afterComparison elementShiftAt →
          IsUnitRotationShift elementShiftAt →
          ∃ blockShift : Block n → ℤ,
            initial.BlocksAlignedWithShift
              (fun element => elementShiftAt element.val)
              blockShift) :
    Nonempty
      (RepresentedTransition params
        (Snapshot.ofTree beforeComparison) splayTree
        (Snapshot.ofTree afterComparison) splayTree initial) := by
  obtain ⟨elementShiftAt, exactUpdate, unitShift⟩ :=
    rotation.existsExactTreeRankUpdate
  obtain ⟨blockShift, blocksAligned⟩ :=
    alignment elementShiftAt exactUpdate unitShift
  let certificate :
      PreparedComparisonRotation
        params splayTree
        (rotationDepth := rotationDepth)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial :=
    { rotation := rotation
      initial_represents := initialRepresents
      elementShiftAt := elementShiftAt
      exactUpdate := exactUpdate
      unitShift := unitShift
      blockShift := blockShift
      prepared := initial
      prefixEvents := []
      prefixTrace := Trace.nil initialRepresents.valid
      rankPrepared := initialRepresents.stable.rankPrepared
      view_eq := viewAlreadyPrepared
      blocksAligned := blocksAligned }
  exact certificate.existsRepresentedTransition

/--
Any constructor for the explicit prepared-prefix certificate is therefore a
complete local comparison-rotation trace realizer.
-/
theorem comparisonRotationTraceRealizer_of_preparer {n : ℕ}
    {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (preparer : ComparisonRotationPreparer params splayTree) :
    ComparisonRotationTraceRealizer params splayTree := by
  intro rotationDepth beforeComparison afterComparison initial
    rotation initialRepresents
  obtain ⟨certificate⟩ :=
    preparer rotation initialRepresents
  exact certificate.existsRepresentedTransition

end Splay.Lazy
