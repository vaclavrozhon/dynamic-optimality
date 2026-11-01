import Splay.Accounting.ArticleRequestPreparation
import Splay.Lazy.CanonicalRankOrder
import Splay.Lazy.IsolatedRankUpdate
import Splay.Lazy.DetachedReparenting

namespace Splay.Accounting

open Splay.Lazy Splay.Lazy.Canonical Splay.Rank Splay.Tree.BST

namespace ArticleRequestPreparation

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
  (preparation : ArticleRequestPreparation params snapshot before key initial)

/-- The two concrete boundary positions selected at the original access. -/
noncomputable def boundarySet (_preparation : ArticleRequestPreparation params snapshot before key initial) : Finset (External n) :=
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  {selection.left, selection.right}

/-- The actual convert/split preparation discharges every isolation condition
needed for a silent change of the two boundary ranks. -/
theorem isolatedRanks : preparation.final.IsolatedRanks preparation.boundarySet := by
  classical
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  have emptyOwner : ∀ block ∈ preparation.final.blocks, block.mode = .growing →
      ∀ owner, ArticleGrowingOwnerEmpty preparation.final owner → block.owner = owner → block.elements = [] := by
    intro block member growing owner empty ownerEq
    obtain ⟨id, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨lt, getEq⟩ := List.getElem?_eq_some_iff.mp found
    let index : Fin preparation.final.blocks.length := ⟨id, lt⟩
    have atSide : ArticleGrowingEmptyAt preparation.final owner block.side := by
      cases block.side with
      | left => exact empty.1
      | right => exact empty.2
    have result := atSide index
    dsimp only at result
    rw [show preparation.final.blocks.get index = block from getEq] at result
    exact result growing ownerEq rfl
  have singleton : ∀ (id : Interface.BlockId) (block : Lazy.Block n) (element : Element n),
      preparation.final.blocks[id]? = some block → block.mode = .shrinking → block.elements = [element] →
      ∀ other ∈ preparation.final.blocks, element ∈ other.elements →
        other.mode = .shrinking ∧ other.elements = [element] := by
    intro id block element found shrinking elements other member inside
    obtain ⟨otherId, otherFound⟩ := List.mem_iff_getElem?.mp member
    have equal := preparation.represents.valid.blockId_eq_of_element_mem found (by simp [elements]) otherFound inside
    rw [← equal, found] at otherFound
    have blocksEqual := Option.some.inj otherFound
    rw [← blocksEqual]
    exact ⟨shrinking, elements⟩
  constructor
  · intro block member growing selected
    have marked : block.owner = selection.left ∨ block.owner = selection.right := by
      simpa [boundarySet, selection] using selected
    rcases marked with left | right
    · exact emptyOwner block member growing _ preparation.leftEmpty left
    · exact emptyOwner block member growing _ preparation.rightEmpty right
  · intro element selected block member inside
    have marked : element = selection.left ∨ element = selection.right := by
      simpa [boundarySet, selection] using selected
    rcases marked with left | right
    · subst element
      exact singleton preparation.leftId preparation.leftBlock selection.left
        preparation.leftFound preparation.leftShrinking preparation.leftElements block member inside
    · subst element
      exact singleton preparation.rightId preparation.rightBlock selection.right
        preparation.rightFound preparation.rightShrinking preparation.rightElements block member inside

theorem boundary_parents (rankZero : snapshot.rank (valuePos key) = 0) :
    ∀ element ∈ preparation.boundarySet,
      preparation.final.view.parent element = some preparation.final.view.root := by
  classical
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection snapshot before key
  have leftMember : selection.left ∈ (canonicalHeapView snapshot before).topDown (valuePos key) .left := by
    rw [canonicalTopDown_eq_proper_filter_append_boundary snapshot before key rankZero]
    simp [selection]
  have rightMember : selection.right ∈ (canonicalHeapView snapshot before).topDown (valuePos key) .right := by
    rw [canonicalTopDown_eq_proper_filter_append_boundary snapshot before key rankZero]
    simp [selection]
  intro element selected
  have marked : element = selection.left ∨ element = selection.right := by
    simpa [boundarySet, selection] using selected
  rw [preparation.represents.view_eq]
  change canonicalParent snapshot before element = some (canonicalRoot snapshot before)
  rw [canonicalRoot_eq_of_rank_eq_zero snapshot before rankZero]
  rcases marked with left | right
  · subst element
    exact ((canonicalHeapView snapshot before).mem_topDown_iff.mp leftMember).1
  · subst element
    exact ((canonicalHeapView snapshot before).mem_topDown_iff.mp rightMember).1

end ArticleRequestPreparation

/-- Before pairing, the actual article preparation lowers both isolated
boundary priorities. Genuine ranks use the fixed doubled coding throughout. -/
structure ArticleTemporaryPreparation {n : ℕ} (params : Interface.Parameters)
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n) (initial : Lazy.State n) where
  rankZero : snapshot.rank (valuePos key) = 0
  preparation : ArticleRequestPreparation params snapshot.withTruePriority before key initial

namespace ArticleTemporaryPreparation

variable {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
  {before : BST 0 n} {key : Fin n} {initial : Lazy.State n}
  (setup : ArticleTemporaryPreparation params snapshot before key initial)

noncomputable def temporarySnapshot : Snapshot n :=
  let selection := WholeSplayTemporaryBoundaryGeometry.KeyFocus.boundaryMinimumSelection
    snapshot.withTruePriority before key
  snapshot.withTwoBoundaryTemporaryPriority selection.left (valuePos key) selection.right
    selection.ordered setup.rankZero

noncomputable def loweredView : HeapView n :=
  setup.preparation.final.view.lowerRootChildren setup.preparation.boundarySet

noncomputable def lowered : Lazy.State n :=
  setup.preparation.final.absorbRankUpdate setup.loweredView
    (setup.preparation.final.isolatedRankBlockShift setup.loweredView)

noncomputable def final : Lazy.State n :=
  setup.lowered.replaceView (canonicalHeapView setup.temporarySnapshot before)

noncomputable def events : List (Event n) := setup.preparation.events ++ [.silent, .silent]

theorem lowered_trace_stable : Trace params setup.preparation.final [.silent] setup.lowered ∧
    setup.lowered.Stable params := by
  apply setup.preparation.isolatedRanks.lowerRootChildren_trace_stable setup.preparation.represents.stable
  · rw [setup.preparation.represents.view_eq]
    exact canonicalHeapView_root_rank _ _
  · apply setup.preparation.boundary_parents
    simp [setup.rankZero]

theorem lowered_rank : setup.loweredView.rank = setup.temporarySnapshot.rank := by
  classical
  funext element
  change (if element ∈ setup.preparation.boundarySet then 1 else setup.preparation.final.view.rank element) = _
  have ranks : setup.preparation.final.view.rank = snapshot.withTruePriority.rank := by
    rw [setup.preparation.represents.view_eq]
    rfl
  rw [ranks]
  simp [temporarySnapshot, ArticleRequestPreparation.boundarySet,
    twoBoundaryTemporaryRank, temporaryPriority, twoBoundaryMarker, artificialPriority]

theorem canonical_agreement :
    (canonicalHeapView setup.temporarySnapshot before).root = setup.loweredView.root ∧
      (canonicalHeapView setup.temporarySnapshot before).parent = setup.loweredView.parent ∧
      (canonicalHeapView setup.temporarySnapshot before).side = setup.loweredView.side := by
  have ordered : ∀ {element owner}, canonicalParent snapshot.withTruePriority before element = some owner →
      setup.temporarySnapshot.rank owner < setup.temporarySnapshot.rank element := by
    intro element owner parent
    have lowOrder : setup.loweredView.HeapOrdered := setup.lowered_trace_stable.2.2.2.1
    rw [← setup.lowered_rank]
    apply lowOrder
    change setup.preparation.final.view.parent element = some owner
    rw [setup.preparation.represents.view_eq]
    exact parent
  have result := canonical_parent_side_eq_of_order snapshot.withTruePriority setup.temporarySnapshot before ordered
  change _ = setup.preparation.final.view.root ∧ _ = setup.preparation.final.view.parent ∧
    _ = setup.preparation.final.view.side
  rw [setup.preparation.represents.view_eq]
  exact result

theorem represents : setup.final.Represents params setup.temporarySnapshot before := by
  refine ⟨?_, rfl⟩
  exact Lazy.State.replaceView_stable setup.lowered_trace_stable.2 _ setup.lowered_rank.symm
    setup.canonical_agreement.1 setup.canonical_agreement.2.1 setup.canonical_agreement.2.2

theorem trace : Trace params initial setup.events setup.final := by
  have rebase : Step params setup.lowered .silent setup.final :=
    Lazy.State.replaceView_step setup.lowered_trace_stable.2.1 _ setup.lowered_rank.symm (by
      intro element _
      exact ⟨congrFun setup.canonical_agreement.2.1 element, congrFun setup.canonical_agreement.2.2 element⟩)
  exact setup.preparation.trace.append
    (setup.lowered_trace_stable.1.append (Trace.cons rebase (Trace.nil setup.represents.valid)))

theorem births : setup.final.blocks.length ≤ initial.blocks.length + 16 := by
  simpa [final, lowered, Lazy.State.replaceView, Lazy.State.absorbRankUpdate] using setup.preparation.births

theorem noInserts : Interface.totalInserts (eraseOperations setup.events) = 0 := by
  rw [events, eraseOperations_append,
    show eraseOperations ([.silent, .silent] : List (Event n)) = [] from rfl, List.append_nil]
  exact setup.preparation.noInserts

theorem noIncreases : Interface.totalIncreases (eraseOperations setup.events) = 0 := by
  rw [events, eraseOperations_append,
    show eraseOperations ([.silent, .silent] : List (Event n)) = [] from rfl, List.append_nil]
  exact setup.preparation.noIncreases

theorem gap_le : geometricGapPotential setup.final ≤ geometricGapPotential initial := by
  have gapEq : geometricGapPotential setup.final = geometricGapPotential setup.preparation.final := by
    rw [geometricGapPotential_eq setup.represents.complete setup.represents.stable.2.2.2.2.2,
      geometricGapPotential_eq setup.preparation.represents.complete setup.preparation.represents.stable.2.2.2.2.2]
    rfl
  rw [gapEq]
  exact setup.preparation.gap_le

/-- Both rank isolation and its actual silent implementation are constructed
from the represented starting state. -/
theorem exists_of_represents {n : ℕ} {params : Interface.Parameters}
    (snapshot : Snapshot n) (before : BST 0 n) (key : Fin n)
    (rankZero : snapshot.rank (valuePos key) = 0) {initial : Lazy.State n}
    (represented : initial.Represents params snapshot.withTruePriority before) :
    Nonempty (ArticleTemporaryPreparation params snapshot before key initial) := by
  obtain ⟨preparation⟩ := ArticleRequestPreparation.exists_preparation snapshot.withTruePriority before key
    (by simp [rankZero]) represented
  exact ⟨⟨rankZero, preparation⟩⟩

end ArticleTemporaryPreparation
end Splay.Accounting
