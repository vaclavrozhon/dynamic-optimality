import Splay.Accounting.CanonicalCrossSideUnbroken

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Lazy.Canonical

namespace CrossSideInformationObstruction

/--
The part of a canonical light edge visible to the current `HeapView`.

In particular, the structural attachment depth used by the manuscript's
cross-side order is deliberately absent.
-/
def edgeSideData {n : ℕ} (edge : Edge n) :
    TernaryBranch × External n × External n × Side :=
  (edge.branch, edge.owner, edge.child, edge.side)

/-- Change only the structural attachment depth of an edge. -/
def edgeAtDepth {n : ℕ} (edge : Edge n) (depth : ℕ) : Edge n where
  branch := edge.branch
  owner := edge.owner
  child := edge.child
  side := edge.side
  attachmentKey := edge.attachmentKey
  attachmentDepth := depth

@[simp]
theorem edgeSideData_atDepth {n : ℕ} (edge : Edge n) (depth : ℕ) :
    edgeSideData (edgeAtDepth edge depth) = edgeSideData edge :=
  rfl

/--
The parent and side facts about an edge that can be checked against a
`HeapView`.  Neither clause mentions attachment depth.
-/
def edgeAgreesWithHeapView {n : ℕ}
    (edge : Edge n) (view : HeapView n) : Prop :=
  view.parent edge.child = some edge.owner ∧
    view.side edge.child = edge.side

@[simp]
theorem Edge.agreesWithHeapView_atDepth_iff {n : ℕ}
    (edge : Edge n) (view : HeapView n) (depth : ℕ) :
    edgeAgreesWithHeapView (edgeAtDepth edge depth) view ↔
      edgeAgreesWithHeapView edge view :=
  Iff.rfl

/-- Three children whose possible interleaving is under consideration. -/
structure EdgeTriple (n : ℕ) where
  first : Edge n
  middle : Edge n
  last : Edge n

namespace EdgeTriple

/-- The complete depth-erased data of a local three-edge configuration. -/
abbrev SideData (n : ℕ) :=
  (TernaryBranch × External n × External n × Side) ×
    (TernaryBranch × External n × External n × Side) ×
      (TernaryBranch × External n × External n × Side)

/-- All data retained by the three side-restricted child lists. -/
def sideData {n : ℕ} (triple : EdgeTriple n) : SideData n :=
  (edgeSideData triple.first,
    edgeSideData triple.middle,
    edgeSideData triple.last)

/-- Compatibility of all three endpoints with one fixed heap view. -/
def AgreesWithHeapView {n : ℕ}
    (triple : EdgeTriple n) (view : HeapView n) : Prop :=
  edgeAgreesWithHeapView triple.first view ∧
    edgeAgreesWithHeapView triple.middle view ∧
      edgeAgreesWithHeapView triple.last view

/--
The local shape relevant to a broken interval: the endpoints have one owner
and side, while the potential separator has the same owner and the opposite
side.
-/
def CrossSideShape {n : ℕ} (triple : EdgeTriple n) : Prop :=
  triple.first.owner = triple.middle.owner ∧
    triple.middle.owner = triple.last.owner ∧
      triple.first.side = triple.last.side ∧
        triple.middle.side ≠ triple.first.side

/-- The middle edge lies strictly between the two endpoint edges. -/
def Broken {n : ℕ} (triple : EdgeTriple n) : Prop :=
  (edgeStrictlyAbove triple.first triple.middle ∧
      edgeStrictlyAbove triple.middle triple.last) ∨
    (edgeStrictlyAbove triple.last triple.middle ∧
      edgeStrictlyAbove triple.middle triple.first)

/--
Once the two unique incoming canonical edges are fixed, child order is
exactly edge attachment-depth order.
-/
theorem childStrictlyAbove_iff_of_incoming
    {n : ℕ} {snapshot : Snapshot n} {tree : Splay.Tree.BST 0 n}
    {first second : Interface.Element n}
    {firstEdge secondEdge : Edge n}
    (firstLookup :
      incomingEdge? snapshot tree first = some firstEdge)
    (secondLookup :
      incomingEdge? snapshot tree second = some secondEdge) :
    ChildStrictlyAbove snapshot tree first second ↔
      edgeStrictlyAbove firstEdge secondEdge := by
  constructor
  · rintro
      ⟨foundFirst, foundSecond, foundFirstLookup,
        foundSecondLookup, above⟩
    have firstEq : firstEdge = foundFirst := by
      rw [firstLookup] at foundFirstLookup
      exact Option.some.inj foundFirstLookup
    have secondEq : secondEdge = foundSecond := by
      rw [secondLookup] at foundSecondLookup
      exact Option.some.inj foundSecondLookup
    simpa only [firstEq, secondEq] using above
  · intro above
    exact
      ⟨firstEdge, secondEdge, firstLookup, secondLookup, above⟩

/--
Exact bridge from the canonical `ChildBetween` relation to the local
attachment-depth triple used by this obstruction.
-/
theorem childBetween_iff_edgeTriple_broken_of_incoming
    {n : ℕ} {snapshot : Snapshot n} {tree : Splay.Tree.BST 0 n}
    {first middle last : Interface.Element n}
    {firstEdge middleEdge lastEdge : Edge n}
    (firstLookup :
      incomingEdge? snapshot tree first = some firstEdge)
    (middleLookup :
      incomingEdge? snapshot tree middle = some middleEdge)
    (lastLookup :
      incomingEdge? snapshot tree last = some lastEdge) :
    ChildBetween snapshot tree first middle last ↔
      (⟨firstEdge, middleEdge, lastEdge⟩ : EdgeTriple n).Broken := by
  constructor
  · intro between
    rcases between with
      ⟨firstAbove, middleAbove⟩ |
      ⟨lastAbove, middleAbove⟩
    · exact Or.inl
        ⟨(childStrictlyAbove_iff_of_incoming
            firstLookup middleLookup).1 firstAbove,
          (childStrictlyAbove_iff_of_incoming
            middleLookup lastLookup).1 middleAbove⟩
    · exact Or.inr
        ⟨(childStrictlyAbove_iff_of_incoming
            lastLookup middleLookup).1 lastAbove,
          (childStrictlyAbove_iff_of_incoming
            middleLookup firstLookup).1 middleAbove⟩
  · intro broken
    rcases broken with
      ⟨firstAbove, middleAbove⟩ |
      ⟨lastAbove, middleAbove⟩
    · exact Or.inl
        ⟨(childStrictlyAbove_iff_of_incoming
            firstLookup middleLookup).2 firstAbove,
          (childStrictlyAbove_iff_of_incoming
            middleLookup lastLookup).2 middleAbove⟩
    · exact Or.inr
        ⟨(childStrictlyAbove_iff_of_incoming
            lastLookup middleLookup).2 lastAbove,
          (childStrictlyAbove_iff_of_incoming
            middleLookup firstLookup).2 middleAbove⟩

/-- Replace the three attachment depths without changing any other field. -/
def atDepths {n : ℕ} (triple : EdgeTriple n)
    (firstDepth middleDepth lastDepth : ℕ) : EdgeTriple n where
  first := edgeAtDepth triple.first firstDepth
  middle := edgeAtDepth triple.middle middleDepth
  last := edgeAtDepth triple.last lastDepth

@[simp]
theorem sideData_atDepths {n : ℕ} (triple : EdgeTriple n)
    (firstDepth middleDepth lastDepth : ℕ) :
    (triple.atDepths firstDepth middleDepth lastDepth).sideData =
      triple.sideData :=
  rfl

@[simp]
theorem agreesWithHeapView_atDepths_iff {n : ℕ}
    (triple : EdgeTriple n) (view : HeapView n)
    (firstDepth middleDepth lastDepth : ℕ) :
    (triple.atDepths firstDepth middleDepth lastDepth).AgreesWithHeapView
        view ↔
      triple.AgreesWithHeapView view :=
  Iff.rfl

@[simp]
theorem crossSideShape_atDepths_iff {n : ℕ}
    (triple : EdgeTriple n)
    (firstDepth middleDepth lastDepth : ℕ) :
    (triple.atDepths firstDepth middleDepth lastDepth).CrossSideShape ↔
      triple.CrossSideShape :=
  Iff.rfl

/--
Putting the potential opposite-side separator below both endpoints makes it
not lie between them.
-/
theorem not_broken_at_depths_zero_two_one {n : ℕ}
    (triple : EdgeTriple n) :
    ¬ (triple.atDepths 0 2 1).Broken := by
  simp [Broken, edgeStrictlyAbove, atDepths, edgeAtDepth]

/--
Putting the opposite-side edge at depth one between endpoint depths zero and
two makes the triple broken.
-/
theorem broken_at_depths_zero_one_two {n : ℕ}
    (triple : EdgeTriple n) :
    (triple.atDepths 0 1 2).Broken := by
  left
  constructor <;>
    simp [edgeStrictlyAbove, atDepths, edgeAtDepth]

/--
Kernel-checked information obstruction.

For every fixed heap view and every compatible cross-side triple, there are
two full attachment-depth completions which:

* agree with exactly the same heap view,
* have identical branch/owner/child/side data,
* retain the same cross-side shape,
* disagree on whether the opposite-side child lies between the endpoints.

Consequently the current side-restricted `HeapView` fields cannot, by
themselves, determine manuscript cross-side brokenness.
-/
theorem same_heapView_data_does_not_determine_brokenness
    {n : ℕ} (view : HeapView n) (triple : EdgeTriple n)
    (agrees : triple.AgreesWithHeapView view)
    (crossSide : triple.CrossSideShape) :
    ∃ outside interleaved : EdgeTriple n,
      outside.AgreesWithHeapView view ∧
        interleaved.AgreesWithHeapView view ∧
        outside.sideData = interleaved.sideData ∧
        outside.CrossSideShape ∧
        interleaved.CrossSideShape ∧
        ¬ outside.Broken ∧
        interleaved.Broken := by
  refine
    ⟨triple.atDepths 0 2 1, triple.atDepths 0 1 2,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (agreesWithHeapView_atDepths_iff triple view 0 2 1).2 agrees
  · exact
      (agreesWithHeapView_atDepths_iff triple view 0 1 2).2 agrees
  · rw [sideData_atDepths, sideData_atDepths]
  · exact
      (crossSideShape_atDepths_iff triple 0 2 1).2 crossSide
  · exact
      (crossSideShape_atDepths_iff triple 0 1 2).2 crossSide
  · exact not_broken_at_depths_zero_two_one triple
  · exact broken_at_depths_zero_one_two triple

/--
The obstruction in functional form: no predicate of only the fixed heap view
and the depth-erased triple data can correctly decide both completions.
-/
theorem no_heapView_sideData_predicate_decides_both
    {n : ℕ} (view : HeapView n) (triple : EdgeTriple n)
    (predict : HeapView n → SideData n → Prop) :
    ¬
      ((predict view (triple.atDepths 0 2 1).sideData ↔
          (triple.atDepths 0 2 1).Broken) ∧
        (predict view (triple.atDepths 0 1 2).sideData ↔
          (triple.atDepths 0 1 2).Broken)) := by
  intro predictsBoth
  have predictsOutsideFalse :
      ¬ predict view (triple.atDepths 0 2 1).sideData := by
    intro predicted
    exact
      (not_broken_at_depths_zero_two_one triple)
        (predictsBoth.1.mp predicted)
  have predictsInterleavedTrue :
      predict view (triple.atDepths 0 1 2).sideData :=
    predictsBoth.2.mpr (broken_at_depths_zero_one_two triple)
  rw [sideData_atDepths] at predictsOutsideFalse predictsInterleavedTrue
  exact predictsOutsideFalse predictsInterleavedTrue

end EdgeTriple

end CrossSideInformationObstruction

end Splay.Accounting
