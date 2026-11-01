import Splay.Lazy.ComparisonRotationPreparation

namespace Splay.Lazy

open Splay.Rank

namespace State.ShiftAtomic

/-- Absorbing a rank update changes neither block modes nor block elements. -/
theorem absorbRankUpdate
    {n : ℕ} {state : State n}
    (atomic : state.ShiftAtomic)
    (afterView : HeapView n) (shift : Block n → ℤ) :
    (state.absorbRankUpdate afterView shift).ShiftAtomic := by
  intro afterBlock afterBlockMem
  simp only [State.absorbRankUpdate] at afterBlockMem
  obtain ⟨beforeBlock, beforeBlockMem, rfl⟩ :=
    List.mem_map.mp afterBlockMem
  rcases atomic beforeBlock beforeBlockMem with growing | shrinking
  · left
    simpa [Block.shiftedInterval] using growing
  · right
    simpa [Block.shiftedInterval] using shrinking

end State.ShiftAtomic

/--
The sole remaining concrete root-swap I/O obligation.

An implementation may realize this with the finite macro

`delete newRoot → silent atomic rebase → safeInsert oldRoot →
 convert singleton → create replacement`.

The endpoint is required to be a genuine post-rotation represented state and
to retain the shift-atomic normal form.  The theorem below automatically
reverses the rank update to the mixed old-rank view required by
`PreparedComparisonRotation`; that algebra is therefore not part of the
builder obligation.
-/
def ComparisonRootSwapBuilder {n : ℕ}
    (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) : Prop :=
  ∀ {beforeComparison afterComparison : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RootRotation beforeComparison afterComparison →
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree →
      initial.ShiftAtomic →
        ∃ swapped events,
          Trace params initial events swapped ∧
            swapped.Represents params
              (Snapshot.ofTree afterComparison) splayTree ∧
            swapped.ShiftAtomic

/--
Comparison-rotation preparation restricted only by the explicit
shift-atomic input invariant.
-/
def ShiftAtomicComparisonRotationPreparer {n : ℕ}
    (params : Interface.Parameters)
    (splayTree : Tree.BST 0 n) : Prop :=
  ∀ {rotationDepth : ℕ}
      {beforeComparison afterComparison : Tree.BST 0 n}
      {initial : State n},
    Tree.BST.RotationAt rotationDepth
        beforeComparison afterComparison →
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree →
      initial.ShiftAtomic →
        Nonempty
          (PreparedComparisonRotation
            params splayTree
            (rotationDepth := rotationDepth)
            (beforeComparison := beforeComparison)
            (afterComparison := afterComparison)
            initial)

/--
A completed root-swap macro yields the exact mixed-rank prepared certificate
for a depth-zero rotation.

The builder ends at true post-rotation ranks.  We use the negative of the
rotation's exact shift to make one silent absorbed update back to the old
numeric ranks, while retaining the post-rotation parent structure.  Atomicity
makes both this reverse update and the certificate's eventual forward update
blockwise uniform.
-/
theorem existsPreparedComparisonRotation_of_rootSwapBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (builder : ComparisonRootSwapBuilder params splayTree)
    {beforeComparison afterComparison : Tree.BST 0 n}
    {initial : State n}
    (rootRotation :
      Tree.BST.RootRotation beforeComparison afterComparison)
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree)
    (initialAtomic : initial.ShiftAtomic) :
    Nonempty
      (PreparedComparisonRotation
        params splayTree
        (rotationDepth := 0)
        (beforeComparison := beforeComparison)
        (afterComparison := afterComparison)
        initial) := by
  obtain ⟨swapped, swapEvents, swapTrace,
      swappedRepresents, swappedAtomic⟩ :=
    builder rootRotation initialRepresents initialAtomic
  let rotation :
      Tree.BST.RotationAt 0 beforeComparison afterComparison :=
    .root rootRotation
  obtain ⟨elementShiftAt, exactUpdate, unitShift⟩ :=
    rotation.existsExactTreeRankUpdate
  let mixedView :=
    Canonical.canonicalHeapViewWithRank
      (Snapshot.ofTree afterComparison)
      (Snapshot.ofTree beforeComparison).rank
      splayTree
  let reverseElementShift : Element n → ℤ :=
    fun element => -elementShiftAt element.val
  let reverseBlockShift : Block n → ℤ :=
    State.shiftAtomicBlockShift reverseElementShift
  have reverseAligned :
      swapped.BlocksAlignedWithShift
        reverseElementShift reverseBlockShift :=
    swappedAtomic.blocksAlignedWithShift reverseElementShift
  have reverseUniform :
      State.BlockwiseUniformRankShift
        swapped mixedView reverseElementShift reverseBlockShift := by
    refine {
      sameStructure := ?_
      rankShift := ?_
      growing := reverseAligned.growing
      shrinking_empty := reverseAligned.shrinking_empty
      shrinking_nonempty := reverseAligned.shrinking_nonempty
    }
    · rw [swappedRepresents.view_eq]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · intro element
      unfold HeapView.RankShift
      change
        ((Snapshot.ofTree beforeComparison).rank element : ℤ) =
          (swapped.view.rank element : ℤ) +
            -elementShiftAt element.val
      rw [swappedRepresents.view_rank_eq]
      have updateAt := exactUpdate element.val
      change
        ((Snapshot.ofTree afterComparison).rank element : ℤ) =
          (Snapshot.ofTree beforeComparison).rank element +
            elementShiftAt element.val
        at updateAt
      omega
  have reverseCompatible :
      swapped.RankUpdateCompatible mixedView reverseBlockShift :=
    reverseUniform.compatible swappedRepresents.valid
  let prepared :=
    swapped.absorbRankUpdate mixedView reverseBlockShift
  have reverseTrace :
      Trace params swapped [.silent] prepared := by
    exact
      swappedRepresents.stable.rankPrepared.absorbRankUpdate_trace
        reverseCompatible
  have rankPrepared : prepared.RankPrepared params := by
    exact
      swappedRepresents.stable.rankPrepared.absorbRankUpdate
        reverseCompatible
  have preparedAtomic : prepared.ShiftAtomic := by
    exact swappedAtomic.absorbRankUpdate mixedView reverseBlockShift
  let blockShift : Block n → ℤ :=
    State.shiftAtomicBlockShift
      (fun element => elementShiftAt element.val)
  have blocksAligned :
      prepared.BlocksAlignedWithShift
        (fun element => elementShiftAt element.val) blockShift :=
    preparedAtomic.blocksAlignedWithShift
      (fun element => elementShiftAt element.val)
  exact
    ⟨{
      rotation := rotation
      initial_represents := initialRepresents
      elementShiftAt := elementShiftAt
      exactUpdate := exactUpdate
      unitShift := unitShift
      blockShift := blockShift
      prepared := prepared
      prefixEvents := swapEvents ++ [.silent]
      prefixTrace := swapTrace.append reverseTrace
      rankPrepared := rankPrepared
      view_eq := rfl
      blocksAligned := blocksAligned
    }⟩

/--
The root-swap builder is the only missing I/O constructor for arbitrary
shift-atomic comparison rotations: positive depths use the concrete silent
rebase already proved in `ComparisonRotationPreparation`.
-/
theorem shiftAtomicComparisonRotationPreparer_of_rootSwapBuilder
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : Tree.BST 0 n}
    (builder : ComparisonRootSwapBuilder params splayTree) :
    ShiftAtomicComparisonRotationPreparer params splayTree := by
  intro rotationDepth beforeComparison afterComparison initial
    rotation initialRepresents initialAtomic
  cases rotation with
  | root rootRotation =>
      exact
        existsPreparedComparisonRotation_of_rootSwapBuilder
          builder rootRotation initialRepresents initialAtomic
  | leftContext inner right =>
      exact
        existsPreparedComparisonRotation_of_shiftAtomic_of_depth_succ
          (.leftContext inner right) initialRepresents initialAtomic
  | rightContext left inner =>
      exact
        existsPreparedComparisonRotation_of_shiftAtomic_of_depth_succ
          (.rightContext left inner) initialRepresents initialAtomic

end Splay.Lazy
