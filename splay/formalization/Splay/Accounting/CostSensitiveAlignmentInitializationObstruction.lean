import Splay.Accounting.AllBoundaryPairingClassification

namespace Splay.Accounting

open Splay.Lazy
open Splay.Rank
open Splay.Tree.BST

/--
A nonempty represented heap cannot simultaneously be an abstract initial
state.

`Represents` is stable and therefore assigns every non-root heap vertex to a
block.  `Interface.State.Initial` requires the block list to be empty.  Since
`Element n` has at least three inhabitants when `0 < n`, these requirements
contradict each other.
-/
theorem represents_not_interfaceInitial_of_pos
    {n : ℕ} (positive : 0 < n)
    {params : Interface.Parameters} {snapshot : Snapshot n}
    {tree : BST 0 n} {state : State n}
    (represents : state.Represents params snapshot tree) :
    ¬state.toInterface.Initial params := by
  intro initial
  obtain ⟨element, elementNeRoot, _⟩ :=
    Fin.exists_ne_and_ne_of_two_lt
      state.view.root state.view.root (by omega)
  have parent :
      state.view.parent element ≠ none :=
    state.view.parent_ne_none_of_ne_root elementNeRoot
  have assigned : element ∈ state.allElements :=
    (represents.complete element).2 parent
  have noAssigned :
      state.toInterface.allElements = [] := by
    simp [Interface.State.allElements, initial.2]
  rw [State.toInterface_allElements] at noAssigned
  rw [noAssigned] at assigned
  simp at assigned

/--
Exact obstruction in the current global endpoint-alignment interface.

`CostSensitivePairingAlignment` asks for a
`BoundaryPassPairingClassification` whose trace starts at the represented
transition's stable initial state.  But the embedded
`PassPairingClassification` requires that same state to be an empty-block
interface initial state.  Thus no such classification exists for `0 < n`,
independently of endpoint geometry or event construction.

The checked repair is the split already used by
`ofInitializedAllImportantSuffix`: run `Initialization.trace` from the empty
state, then attach represented provenance and boundary moves to its stable
suffix.
-/
theorem no_boundaryPassClassification_on_represented_initial_of_pos
    {n : ℕ} (positive : 0 < n)
    {params : Interface.Parameters} {snapshot : Snapshot n}
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
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    False := by
  exact
    represents_not_interfaceInitial_of_pos positive
      transition.initial_represents
      classification.passClassification.initialState

/-- In particular, the current cost-sensitive alignment record is empty. -/
theorem no_costSensitivePairingAlignment_of_pos
    {n : ℕ} (positive : 0 < n)
    {params : Interface.Parameters} {snapshot : Snapshot n}
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
    (provenance :
      SplaySequence.RepresentedTransitionProvenance
        sequence transition)
    (classification :
      BoundaryPassPairingClassification transcript params
        initial transition.final transition.events) :
    ¬CostSensitivePairingAlignment transcript provenance
      classification := by
  intro _alignment
  exact
    no_boundaryPassClassification_on_represented_initial_of_pos
      positive classification

end Splay.Accounting
