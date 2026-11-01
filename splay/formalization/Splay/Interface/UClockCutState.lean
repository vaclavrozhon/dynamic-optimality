import Splay.Interface.UColumnIncidence
import Splay.Interface.UClockCutList
import Splay.Interface.RootLineagePhase

namespace Splay.Interface

/-- A block contains the unique geometric boundary selected by one clock cut. -/
def BlockClockMixedAt {n : ℕ} (clock : EpisodeClock n) (cutoff : ℕ)
    (block : Block n) : Prop :=
  ∃ first second,
    Adjacent block.elements first second ∧
      ClockStraddlesAt clock cutoff first second

theorem BlockClockMixedAt.elements_ne_nil
    {n : ℕ} {clock : EpisodeClock n} {cutoff : ℕ}
    {block : Block n}
    (mixed : BlockClockMixedAt clock cutoff block) :
    block.elements ≠ [] := by
  obtain ⟨first, second, adjacent, straddles⟩ := mixed
  intro empty
  rw [empty] at adjacent
  obtain ⟨front, back, ordered | reversed⟩ := adjacent
  · have lengthEq := congrArg List.length ordered
    simp at lengthEq
  · have lengthEq := congrArg List.length reversed
    simp at lengthEq

/--
A mixed block in a lineage whose realized root block is still growing must be
that root block itself.
-/
theorem RootLineagePhase.mixed_block_eq_root_of_growing
    {n : ℕ} {state : State n} {labels : RootLabels}
    (phase : RootLineagePhase state labels)
    {clock : EpisodeClock n} {cutoff : ℕ}
    {root blockId : RootId} {rootBlock block : Block n}
    (rootFound : state.block? root = some rootBlock)
    (rootGrowing : rootBlock.mode = .growing)
    (blockFound : state.block? blockId = some block)
    (labelFound : RootLabels.root? labels blockId = some root)
    (mixed : BlockClockMixedAt clock cutoff block) :
    blockId = root :=
  phase.growingOnly root rootBlock rootFound rootGrowing
    blockId block blockFound labelFound mixed.elements_ne_nil

/-- Every live block is monotone across the selected chronological cut. -/
def StateClockCutOrderedAt {n : ℕ} (state : State n)
    (clock : EpisodeClock n) (cutoff : ℕ) : Prop :=
  ∀ blockId block,
    state.block? blockId = some block →
      ClockCutOrderedAt clock cutoff block.elements

/-- At most one block of a root lineage contains the selected clock boundary. -/
def RootClockCutUniqueAt {n : ℕ} (state : State n)
    (labels : RootLabels) (clock : EpisodeClock n) (cutoff : ℕ) : Prop :=
  ∀ root firstId firstBlock secondId secondBlock,
    state.block? firstId = some firstBlock →
      RootLabels.root? labels firstId = some root →
      BlockClockMixedAt clock cutoff firstBlock →
      state.block? secondId = some secondBlock →
      RootLabels.root? labels secondId = some root →
      BlockClockMixedAt clock cutoff secondBlock →
      firstId = secondId

/--
Every already emitted crossing key lies strictly below the pass counter of the
current boundary block of the same root.  This is the pass-floor component
that makes the next boundary pass fresh.
-/
def CrossingKeyBelowCutAt {n : ℕ} (state : State n)
    (labels : RootLabels) (clock : EpisodeClock n) (cutoff : ℕ)
    (past : List LineageRunKey) : Prop :=
  ∀ key ∈ past, ∀ blockId block,
    state.block? blockId = some block →
      RootLabels.root? labels blockId = some key.1 →
      BlockClockMixedAt clock cutoff block →
      key.2 < block.passCount

/--
Every root already charged by a crossing pass has irreversibly entered its
shrinking phase.  This prevents a later pass destination, whose root is still
growing, from reviving an old key root after the boundary temporarily
disappeared.
-/
def CrossingKeyRootsShrinkingAt {n : ℕ} (state : State n)
    (past : List LineageRunKey) : Prop :=
  ∀ key ∈ past,
    ∃ rootBlock,
      state.block? key.1 = some rootBlock ∧
        rootBlock.mode = .shrinking

/-- The complete fixed-cut accumulator carried by the history induction. -/
structure ClockCrossingAccumulatorAt {n : ℕ} (state : State n)
    (labels : RootLabels) (clock : EpisodeClock n) (cutoff : ℕ)
    (past : List LineageRunKey) : Prop where
  ordered : StateClockCutOrderedAt state clock cutoff
  unique : RootClockCutUniqueAt state labels clock cutoff
  keysNodup : past.Nodup
  pastBelow : CrossingKeyBelowCutAt state labels clock cutoff past
  pastRootsShrinking : CrossingKeyRootsShrinkingAt state past

namespace ClockCrossingAccumulatorAt

/-- The empty concrete start carries the fixed-cut invariant for every cut. -/
theorem initial {n : ℕ} (state : State n) (clock : EpisodeClock n)
    (cutoff : ℕ) (empty : state.blocks = []) :
    ClockCrossingAccumulatorAt state [] clock cutoff [] := by
  constructor
  · intro blockId block found
    simp [State.block?, empty] at found
  · intro root firstId firstBlock secondId secondBlock firstFound
    simp [State.block?, empty] at firstFound
  · simp
  · intro key keyMem
    simp at keyMem
  · intro key keyMem
    simp at keyMem

end ClockCrossingAccumulatorAt

end Splay.Interface
