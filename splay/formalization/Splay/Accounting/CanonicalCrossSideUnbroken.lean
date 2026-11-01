import Splay.Accounting.RequestStartBoundaryLineage
import Splay.Accounting.FullOrderSegment

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST
open Splay.Lazy.Canonical

/--
Strict top-down order of two canonical light-edge attachments.

Smaller structural depth is higher.  At the same internal node, a middle
edge is below a left or right edge, exactly as in the manuscript's full
top-down convention.  The two outer branches at one node have the same
attachment height and are intentionally incomparable.
-/
def edgeStrictlyAbove {n : ℕ} (first second : Edge n) : Prop :=
  first.attachmentDepth < second.attachmentDepth ∨
    (first.attachmentDepth = second.attachmentDepth ∧
      first.branch ≠ .middle ∧ second.branch = .middle)

theorem edgeStrictlyAbove_asymm
    {n : ℕ} {first second : Edge n}
    (above : edgeStrictlyAbove first second) :
    ¬ edgeStrictlyAbove second first := by
  intro reverse
  unfold edgeStrictlyAbove at above reverse
  rcases above with depthLt | ⟨depthEq, firstOuter, secondMiddle⟩
  · rcases reverse with reverseLt | ⟨reverseEq, _, _⟩
    · omega
    · omega
  · rcases reverse with reverseLt | ⟨reverseEq, secondOuter, _⟩
    · omega
    · exact secondOuter secondMiddle

/-- One canonical heap child is attached strictly above another. -/
def ChildStrictlyAbove {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n)
    (first second : Interface.Element n) : Prop :=
  ∃ firstEdge secondEdge,
    incomingEdge? snapshot tree first = some firstEdge ∧
      incomingEdge? snapshot tree second = some secondEdge ∧
      edgeStrictlyAbove firstEdge secondEdge

theorem ChildStrictlyAbove.asymm
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {first second : Interface.Element n}
    (above : ChildStrictlyAbove snapshot tree first second) :
    ¬ ChildStrictlyAbove snapshot tree second first := by
  rintro ⟨secondEdge, firstEdge, secondFound, firstFound, reverse⟩
  obtain ⟨firstEdge', secondEdge', firstFound', secondFound', forward⟩ :=
    above
  have firstEq : firstEdge' = firstEdge := by
    rw [firstFound] at firstFound'
    exact Option.some.inj firstFound'.symm
  have secondEq : secondEdge' = secondEdge := by
    rw [secondFound] at secondFound'
    exact Option.some.inj secondFound'.symm
  subst firstEdge'
  subst secondEdge'
  exact edgeStrictlyAbove_asymm forward reverse

/-- `middle` lies strictly between the other two children in full top-down order. -/
def ChildBetween {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n)
    (first middle last : Interface.Element n) : Prop :=
  (ChildStrictlyAbove snapshot tree first middle ∧
      ChildStrictlyAbove snapshot tree middle last) ∨
    (ChildStrictlyAbove snapshot tree last middle ∧
      ChildStrictlyAbove snapshot tree middle first)

/--
A concrete lazy interval is unbroken in the manuscript's cross-side sense:
no child on the opposite side of its owner is attached strictly between two
of its elements in the full top-down order.

This definition deliberately uses canonical light-edge attachment depths,
information which is absent from `HeapView.topDown` (that field stores only
the two side-restricted lists).
-/
def canonicalBlockCrossSideUnbroken {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n)
    (block : Lazy.Block n) : Prop :=
  ∀ first ∈ block.elements, ∀ last ∈ block.elements, ∀ middle,
    canonicalParent snapshot tree middle = some block.owner →
      canonicalSide snapshot tree middle ≠ block.side →
        ¬ ChildBetween snapshot tree first middle last

/-- A certified top-down order of canonical children of one heap owner. -/
structure CanonicalChildOrder {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n)
    (owner : Interface.Element n) where
  elements : List (Interface.Element n)
  nodup : elements.Nodup
  parent :
    ∀ element ∈ elements,
      canonicalParent snapshot tree element = some owner
  between :
    ∀ first middle last,
      ListBetween elements first middle last →
        ChildBetween snapshot tree first middle last

/--
A concrete full top-down order of all currently assigned heap children of
one canonical heavy-path owner.

The side projections are exactly the two lists already stored by `HeapView`;
the inherited order fields restore the cross-side attachment ordering that
those two separate projections intentionally erase.
-/
structure CanonicalFullTopDownOrder {n : ℕ}
    (snapshot : Snapshot n) (tree : BST 0 n)
    (assigned : List (Interface.Element n))
    (owner : Interface.Element n)
    extends CanonicalChildOrder snapshot tree owner where
  sideProjection :
    ∀ side,
      elements.filter
          (fun element => decide (canonicalSide snapshot tree element = side)) =
        (canonicalHeapView snapshot tree).attachedTopDown
          assigned owner side

/--
Article-faithful bridge for a child order that may already omit the isolated
`x⁻` and `x⁺` boundary singletons.  This is the form used after Step 2 of the
manuscript scheduler.
-/
theorem canonicalBlock_isSegment_childOrder
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {block : Lazy.Block n}
    (order : CanonicalChildOrder snapshot tree block.owner)
    (sideSegment :
      IsSegment block.elements
        (order.elements.filter
          (fun element => decide
            (canonicalSide snapshot tree element = block.side))))
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block) :
    IsSegment block.elements order.elements := by
  apply isSegment_of_filter_segment_of_unbroken
    (predicate := fun element =>
      decide (canonicalSide snapshot tree element = block.side))
  · exact sideSegment
  · exact order.nodup
  · intro first firstMember last lastMember middle opposite between
    have middleMember : middle ∈ order.elements := between.middle_mem
    have middleParent := order.parent middle middleMember
    have middleOpposite :
        canonicalSide snapshot tree middle ≠ block.side := by
      simpa using opposite
    exact
      unbroken first firstMember last lastMember middle
        middleParent middleOpposite (order.between _ _ _ between)

/--
Article-faithful bridge from side-consecutiveness plus `unbroken` to genuine
consecutiveness in the full interleaved top-down order.
-/
theorem canonicalBlock_isSegment_fullTopDown
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {assigned : List (Interface.Element n)} {block : Lazy.Block n}
    (structural :
      block.StructurallyValid
        (canonicalHeapView snapshot tree) assigned)
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block)
    (order :
      CanonicalFullTopDownOrder snapshot tree assigned block.owner) :
    IsSegment block.elements order.elements := by
  apply canonicalBlock_isSegment_childOrder
    (order := order.toCanonicalChildOrder)
  · rw [order.sideProjection block.side]
    exact structural.isSegment
  · exact unbroken

theorem canonicalBlockCrossSideUnbroken_of_elements_nil
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (block : Lazy.Block n) (empty : block.elements = []) :
    canonicalBlockCrossSideUnbroken snapshot tree block := by
  intro first firstMem
  rw [empty] at firstMem
  simp at firstMem

theorem canonicalBlockCrossSideUnbroken_of_elements_singleton
    {n : ℕ} (snapshot : Snapshot n) (tree : BST 0 n)
    (block : Lazy.Block n) (element : Interface.Element n)
    (singleton : block.elements = [element]) :
    canonicalBlockCrossSideUnbroken snapshot tree block := by
  intro first firstMem last lastMem middle parent opposite
  have firstEq : first = element := by
    simpa [singleton] using firstMem
  have lastEq : last = element := by
    simpa [singleton] using lastMem
  subst first
  subst last
  intro between
  rcases between with ⟨above, below⟩ | ⟨above, below⟩
  · exact ChildStrictlyAbove.asymm above below
  · exact ChildStrictlyAbove.asymm above below

/--
Cross-side unbrokenness is hereditary under shrinking the payload while
keeping the same owner and side.  This is the exact fact needed for delete,
pass, and both children of a split.
-/
theorem canonicalBlockCrossSideUnbroken_mono
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {before after : Lazy.Block n}
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree before)
    (ownerEq : after.owner = before.owner)
    (sideEq : after.side = before.side)
    (subset : ∀ element ∈ after.elements, element ∈ before.elements) :
    canonicalBlockCrossSideUnbroken snapshot tree after := by
  intro first firstMember last lastMember middle parent opposite
  apply unbroken first (subset first firstMember) last (subset last lastMember)
    middle
  · simpa only [ownerEq] using parent
  · simpa only [sideEq] using opposite

theorem canonicalBlockCrossSideUnbroken_converted
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {block : Lazy.Block n} {intervalGap : ℤ}
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block) :
    canonicalBlockCrossSideUnbroken snapshot tree
      (block.converted intervalGap) := by
  exact canonicalBlockCrossSideUnbroken_mono unbroken rfl rfl
    (fun _ member => member)

theorem canonicalBlockCrossSideUnbroken_deleted
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {block : Lazy.Block n} {element : Interface.Element n}
    {intervalGap : ℤ}
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block) :
    canonicalBlockCrossSideUnbroken snapshot tree
      (block.deleted element intervalGap) := by
  apply canonicalBlockCrossSideUnbroken_mono
    (after := block.deleted element intervalGap) unbroken rfl rfl
  intro member memberAfter
  exact List.mem_of_mem_erase memberAfter

theorem canonicalBlockCrossSideUnbroken_splitPrefix
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {block : Lazy.Block n} {count : ℕ} {intervalGap : ℤ}
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block) :
    canonicalBlockCrossSideUnbroken snapshot tree
      (block.splitPrefix count intervalGap) := by
  apply canonicalBlockCrossSideUnbroken_mono
    (after := block.splitPrefix count intervalGap) unbroken rfl rfl
  intro element member
  exact (List.take_sublist count block.elements).mem member

theorem canonicalBlockCrossSideUnbroken_splitSuffix
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {block : Lazy.Block n} {count : ℕ} {intervalGap : ℤ}
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block) :
    canonicalBlockCrossSideUnbroken snapshot tree
      (block.splitSuffix count intervalGap) := by
  apply canonicalBlockCrossSideUnbroken_mono
    (after := block.splitSuffix count intervalGap) unbroken rfl rfl
  intro element member
  exact (List.drop_sublist count block.elements).mem member

theorem canonicalBlockCrossSideUnbroken_afterPassSource
    {n : ℕ} {snapshot : Snapshot n} {tree : BST 0 n}
    {block : Lazy.Block n}
    {matching : List (Interface.Pairing n)} {intervalGap : ℤ}
    (unbroken : canonicalBlockCrossSideUnbroken snapshot tree block) :
    canonicalBlockCrossSideUnbroken snapshot tree
      (block.afterPassSource matching intervalGap) := by
  apply canonicalBlockCrossSideUnbroken_mono
    (after := block.afterPassSource matching intervalGap) unbroken rfl rfl
  intro element member
  unfold Lazy.Block.afterPassSource at member
  unfold Interface.removeLosers at member
  have foldSubset :
      ∀ (pairs : List (Interface.Pairing n))
          (remaining : List (Interface.Element n))
          (candidate : Interface.Element n),
        candidate ∈
            pairs.foldl
              (fun current pairing => current.erase pairing.loser)
              remaining →
          candidate ∈ remaining := by
    intro pairs
    induction pairs with
    | nil =>
        intro remaining candidate candidateMember
        exact candidateMember
    | cons pairing pairs ih =>
        intro remaining candidate candidateMember
        simp only [List.foldl_cons] at candidateMember
        exact List.mem_of_mem_erase
          (ih (remaining.erase pairing.loser) candidate candidateMember)
  exact foldSubset matching block.elements element member

namespace RequestStartSource

variable
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)}
    {beforeTree afterTree : BST 0 n}
    {sequence : SplaySequence accesses beforeTree afterTree}
    {kinds : List SplayStepKind} {zig zigZig zigZag : ℕ}
    {transcript :
      SplaySequenceTranscript sequence kinds zig zigZig zigZag}
    {initial : State n}
    {transition :
      RepresentedTransition params
        snapshot beforeTree snapshot afterTree initial}
    {provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition}
    {slot : PairingSlot}
    {winner loser : Interface.Element n}
    {agreement :
      RealizedPairingEndpointAgreement transcript provenance
        slot winner loser}
    {request :
      SplaySequenceTranscript.RealizedRequestAt provenance
        agreement.endpoints.realized.occurrence.occurrence}
    {initialLabels : Interface.RootLabels}

/-- The automatically selected source ID is also in range in the rich block list. -/
theorem source_lt
    (sourceAt :
      RequestStartSource agreement request initialLabels) :
    sourceAt.source < request.requestInitial.blocks.length := by
  have interfaceLt :
      sourceAt.source <
        request.requestInitial.toInterface.blocks.length :=
    (List.getElem?_eq_some_iff.mp sourceAt.sourceFound).1
  simpa [Lazy.State.toInterface] using interfaceLt

/-- The exact rich lazy interval containing the loser at request start. -/
def richSourceBlock
    (sourceAt :
      RequestStartSource agreement request initialLabels) :
    Lazy.Block n :=
  request.requestInitial.blocks.get
    ⟨sourceAt.source, sourceAt.source_lt⟩

theorem richSourceFound
    (sourceAt :
      RequestStartSource agreement request initialLabels) :
    request.requestInitial.blocks[sourceAt.source]? =
      some sourceAt.richSourceBlock :=
  List.getElem?_eq_getElem sourceAt.source_lt

/-- Rich and erased source blocks have exactly the same payload. -/
theorem richSourceBlock_elements
    (sourceAt :
      RequestStartSource agreement request initialLabels) :
    sourceAt.richSourceBlock.elements =
      sourceAt.sourceBlock.elements := by
  have mappedFound :
      request.requestInitial.toInterface.blocks[sourceAt.source]? =
        some sourceAt.richSourceBlock.toInterface := by
    simp [Lazy.State.toInterface, sourceAt.richSourceFound]
  have sourceFound := sourceAt.sourceFound
  unfold Interface.State.block? at sourceFound
  rw [sourceFound] at mappedFound
  have blockEq :
      sourceAt.richSourceBlock.toInterface = sourceAt.sourceBlock :=
    Option.some.inj mappedFound.symm
  exact congrArg Interface.Block.elements blockEq

/-- The rich source is a genuine side-consecutive interval in the request view. -/
theorem richSourceBlock_structurallyValid
    (sourceAt :
      RequestStartSource agreement request initialLabels) :
    sourceAt.richSourceBlock.StructurallyValid
      request.requestInitial.view request.requestInitial.allElements := by
  exact
    request.requestTransition.initial_represents.valid.2
      sourceAt.richSourceBlock
      (List.mem_of_getElem? sourceAt.richSourceFound)

/-- Automatic cross-side unbrokenness proposition for the original loser interval. -/
def Unbroken
    (sourceAt :
      RequestStartSource agreement request initialLabels) : Prop :=
  canonicalBlockCrossSideUnbroken snapshot
    agreement.endpoints.realized.occurrence.requestBefore
    sourceAt.richSourceBlock

/-- Manuscript-shaped unimportant case with no semantic `unbrokenAt` field. -/
def Unimportant
    (sourceAt :
      RequestStartSource agreement request initialLabels)
    (cutoff : ℕ) : Prop :=
  sourceAt.Unbroken ∧ cutoff ≤ sourceAt.richSourceBlock.elements.length

/-- Important is the exact complement of the automatic creation-side case. -/
def Important
    (sourceAt :
      RequestStartSource agreement request initialLabels)
    (cutoff : ℕ) : Prop :=
  ¬ sourceAt.Unimportant cutoff

end RequestStartSource

end Splay.Accounting
