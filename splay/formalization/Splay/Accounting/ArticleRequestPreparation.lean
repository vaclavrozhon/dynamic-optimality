import Splay.Accounting.ArticleGlobalPairingEnumeration
import Splay.Accounting.ArticleGapPotential
import Splay.Accounting.ArticleFiniteIsolation
import Splay.Accounting.ArticleFiniteGrowingPreparation

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST Splay.Lazy.Canonical

/-- The actual preparation prefix of one article request. Boundary block IDs
and all subsequent costs refer to this same constructed state. -/
structure ArticleRequestPreparation {n : ℕ} (params : Interface.Parameters)
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n) (initial : Lazy.State n) where
  events : List (Event n)
  final : Lazy.State n
  trace : Trace params initial events final
  represents : final.Represents params snapshot before
  births : final.blocks.length ≤ initial.blocks.length + 16
  noInserts : Interface.totalInserts (eraseOperations events) = 0
  noIncreases : Interface.totalIncreases (eraseOperations events) = 0
  passRefines : initial.PassRefinement final
  gap_le : geometricGapPotential final ≤ geometricGapPotential initial
  accessedEmpty : ArticleGrowingOwnerEmpty final (valuePos key)
  leftEmpty : ArticleGrowingOwnerEmpty final
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).left
  rightEmpty : ArticleGrowingOwnerEmpty final
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).right
  leftId : Interface.BlockId
  rightId : Interface.BlockId
  leftBlock : Lazy.Block n
  rightBlock : Lazy.Block n
  leftFound : final.blocks[leftId]? = some leftBlock
  leftShrinking : leftBlock.mode = .shrinking
  leftElements : leftBlock.elements =
    [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).left]
  leftGap : leftBlock.intervalGap = initial.view.rawGap
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).left
  leftValue : final.value
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).left = 1
  rightFound : final.blocks[rightId]? = some rightBlock
  rightShrinking : rightBlock.mode = .shrinking
  rightElements : rightBlock.elements =
    [(WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).right]
  rightGap : rightBlock.intervalGap = initial.view.rawGap
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).right
  rightValue : final.value
    (WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key).right = 1

namespace ArticleRequestPreparation

/-- Isolate both boundaries and empty the six required growing slots.
The actual finite constructions preserve all positive-pass ancestry. -/
theorem exists_preparation {n : ℕ} {params : Interface.Parameters}
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n)
    (rankZero : snapshot.rank (valuePos key) = 0) {initial : Lazy.State n}
    (represented : initial.Represents params snapshot before) :
    Nonempty (ArticleRequestPreparation params snapshot before key initial) := by
  classical
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  obtain ⟨isolation⟩ := ArticleFiniteIsolation.exists_finite represented.stable [selection.left, selection.right]
  let slots : List (Element n × Side) :=
    [(valuePos key, .left), (valuePos key, .right), (selection.left, .left),
      (selection.left, .right), (selection.right, .left), (selection.right, .right)]
  obtain ⟨growings⟩ := ArticleFiniteGrowingPreparation.exists_finite isolation.stable slots
  have finalView : growings.final.view = initial.view := growings.view_eq.trans isolation.view_eq
  have finalRepresents : growings.final.Represents params snapshot before :=
    ⟨growings.stable, finalView.trans represented.view_eq⟩
  have singletons := growings.singletons isolation.stable.2.1 isolation.singletons
  have data : ∀ element ∈ [selection.left, selection.right],
      ∃ (id : Interface.BlockId) (block : Lazy.Block n), growings.final.blocks[id]? = some block ∧ block.mode = .shrinking ∧
        block.elements = [element] ∧ block.intervalGap = initial.view.rawGap element ∧
        growings.final.value element = 1 := by
    intro element marked
    have notRoot : element ≠ canonicalRoot snapshot before := by
      rw [canonicalRoot_eq_of_rank_eq_zero snapshot before rankZero]
      rcases List.mem_cons.mp marked with equal | rest
      · exact equal ▸ ne_of_lt selection.ordered.1
      · have equal := List.mem_singleton.mp rest
        exact equal ▸ ne_of_gt selection.ordered.2
    have assigned : element ∈ growings.final.allElements := by
      apply (growings.stable.2.1 element).mpr
      rw [finalRepresents.view_eq]
      exact (canonicalHeapView snapshot before).parent_ne_none_of_ne_root notRoot
    obtain ⟨block, member, inside⟩ := State.mem_allElements_iff.mp assigned
    obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨shrinking, singleton⟩ := singletons element (List.mem_toFinset.mpr marked) block member inside
    have gapValid := (growings.stable.1.2 block member).2.2
    simp only [Block.GapValid, shrinking] at gapValid
    have gap : block.intervalGap = growings.final.view.rawGap element := by
      rcases gapValid with empty | nonempty
      · simp [singleton] at empty
      · obtain ⟨minimum, minimumIn, attained⟩ := nonempty.2.1
        have equal : minimum = element := by simpa [singleton] using minimumIn
        subst minimum
        exact attained.symm
    refine ⟨id, block, found, shrinking, singleton, ?_, ?_⟩
    · simpa only [finalView] using gap
    · rw [growings.stable.2.2.2.2.2.2 block member element inside, gap]
      exact Analysis.transientContractedGap_self _
  obtain ⟨leftId, leftBlock, leftFound, leftShrinking, leftElements, leftGap, leftValue⟩ :=
    data selection.left (by simp)
  obtain ⟨rightId, rightBlock, rightFound, rightShrinking, rightElements, rightGap, rightValue⟩ :=
    data selection.right (by simp)
  let events := isolation.events ++ growings.events
  have trace : Trace params initial events growings.final := isolation.trace.append growings.trace
  have noInserts : Interface.totalInserts (eraseOperations events) = 0 := by
    rw [show events = isolation.events ++ growings.events from rfl, eraseOperations_append,
      Interface.totalInserts_append, isolation.noInserts, growings.noInserts]
  have noIncreases : Interface.totalIncreases (eraseOperations events) = 0 := by
    rw [show events = isolation.events ++ growings.events from rfl, eraseOperations_append,
      Interface.totalIncreases_append, isolation.noIncreases, growings.noIncreases]
  exact ⟨{
    events := events
    final := growings.final
    trace := trace
    represents := finalRepresents
    births := by
      have isolationBound := isolation.births
      have growingBound := growings.births
      norm_num [slots] at isolationBound growingBound
      omega
    noInserts := noInserts
    noIncreases := noIncreases
    passRefines := isolation.passRefines.trans growings.passRefines
    gap_le := geometricGapPotential_le_of_no_increases represented.stable growings.stable trace noIncreases
    accessedEmpty := ⟨growings.empty (valuePos key, .left) (by simp [slots]), growings.empty (valuePos key, .right) (by simp [slots])⟩
    leftEmpty := ⟨growings.empty (selection.left, .left) (by simp [slots]), growings.empty (selection.left, .right) (by simp [slots])⟩
    rightEmpty := ⟨growings.empty (selection.right, .left) (by simp [slots]), growings.empty (selection.right, .right) (by simp [slots])⟩
    leftId, rightId, leftBlock, rightBlock, leftFound, leftShrinking, leftElements, leftGap, leftValue,
    rightFound, rightShrinking, rightElements, rightGap, rightValue
  }⟩

end ArticleRequestPreparation

/-- A constructed preparation followed by the complete ready-source worklist.
Coverage here is exactly coverage of ready sources; boundary and exempt
pairings still belong to the remaining request phases. -/
structure ArticleInternalPrefix {n : ℕ} (params : Interface.Parameters)
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n)
    (kinds : List SplayStepKind) (initial : Lazy.State n) where
  preparation : ArticleRequestPreparation params snapshot before key initial
  worklist : ArticleReadyWorklistExecution
    (articleReadySourceWorklist key.val snapshot before kinds params preparation.final)

namespace ArticleInternalPrefix

def events {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (execution : ArticleInternalPrefix params snapshot before key kinds initial) : List (Event n) :=
  execution.preparation.events ++ execution.worklist.chain.events

theorem trace {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (execution : ArticleInternalPrefix params snapshot before key kinds initial) :
    Trace params initial execution.events execution.worklist.chain.final :=
  execution.preparation.trace.append execution.worklist.chain.trace

theorem births {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (execution : ArticleInternalPrefix params snapshot before key kinds initial) :
    execution.worklist.chain.final.blocks.length ≤ initial.blocks.length + 16 := by
  rw [execution.worklist.chain.blocks_length_eq]
  exact execution.preparation.births

theorem noInserts {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (execution : ArticleInternalPrefix params snapshot before key kinds initial) :
    Interface.totalInserts (eraseOperations execution.events) = 0 := by
  change Interface.totalInserts (eraseOperations (execution.preparation.events ++ execution.worklist.chain.events)) = 0
  have appendCount : ∀ a b : List (Interface.Operation n),
      Interface.totalInserts (a ++ b) = Interface.totalInserts a + Interface.totalInserts b := by
    intros; simp [Interface.totalInserts]
  simp only [eraseOperations_append, appendCount, execution.preparation.noInserts,
    execution.worklist.chain.inserts_eq_zero, Nat.zero_add]

theorem gap_pays_increases {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {before : BST 0 n} {key : Fin n} {kinds : List SplayStepKind} {initial : Lazy.State n}
    (execution : ArticleInternalPrefix params snapshot before key kinds initial) :
    geometricGapPotential execution.worklist.chain.final +
        Interface.totalIncreases (eraseOperations execution.events) ≤ geometricGapPotential initial := by
  have appendCount : ∀ a b : List (Interface.Operation n),
      Interface.totalIncreases (a ++ b) = Interface.totalIncreases a + Interface.totalIncreases b := by
    intros; simp [Interface.totalIncreases]
  simp only [events, eraseOperations_append, appendCount, execution.preparation.noIncreases,
    Nat.zero_add, execution.worklist.chain.increases_eq_good]
  exact execution.worklist.chain.gap_drop.trans execution.preparation.gap_le

theorem exists_prefix {n : ℕ} {params : Interface.Parameters}
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n)
    (kinds : List SplayStepKind) (rankZero : snapshot.rank (valuePos key) = 0)
    {initial : Lazy.State n} (represented : initial.Represents params snapshot before)
    (fraction : 10 * params.matchingNumerator ≤ params.matchingDenominator) :
    Nonempty (ArticleInternalPrefix params snapshot before key kinds initial) := by
  obtain ⟨preparation⟩ := ArticleRequestPreparation.exists_preparation snapshot before key rankZero represented
  have rankEq : preparation.final.view.rank = snapshot.rank := by
    rw [preparation.represents.view_eq]
    rfl
  obtain ⟨worklist⟩ := exists_completeReadySourceWorklistExecution
    (key := key.val) (before := before) (kinds := kinds)
    preparation.represents.stable rankEq fraction
  exact ⟨⟨preparation, worklist⟩⟩

end ArticleInternalPrefix
end Splay.Accounting
