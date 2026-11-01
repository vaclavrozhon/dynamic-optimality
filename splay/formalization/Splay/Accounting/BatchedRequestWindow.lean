import Splay.Accounting.SplayRequestProvenance
import Splay.Accounting.RequestStartBoundaryLineage

namespace Splay.Accounting

open Splay.Lazy Splay.Rank Splay.Tree.BST

namespace SplaySequenceTranscript

/-- The exact complete-request window for a zig-zig in a batched realization. -/
structure BatchedRequestAt
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
    (provenance :
      SplaySequence.RequestTransitionProvenance
        sequence transition)
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex
        stepBefore stepAfter depth) : Type where
  prefixTransition :
    RepresentedTransition params
      snapshot beforeTree snapshot requestBefore initial
  requestInitial : State n
  prefix_final_eq : prefixTransition.final = requestInitial
  requestTransition :
    RepresentedTransition params
      snapshot requestBefore snapshot requestAfter requestInitial
  suffixTransition :
    RepresentedTransition params
      snapshot requestAfter snapshot afterTree requestTransition.final
  events_eq :
    transition.events =
      prefixTransition.events ++ requestTransition.events ++
        suffixTransition.events
  final_eq : suffixTransition.final = transition.final

namespace BatchedRequestAt

/--
Sequence provenance automatically exposes the complete request containing
the selected zig-zig, including the exact rich state at request start.
The proof uses only request boundaries; pairing batches may span splay steps.
-/
theorem exists_of_provenance
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
    (provenance :
      SplaySequence.RequestTransitionProvenance
        sequence transition)
    {globalIndex requestIndex : ℕ} {access : Fin n}
    {requestBefore requestAfter : BST 0 n}
    {localIndex depth : ℕ} {stepBefore stepAfter : BST 0 n}
    (occurrence :
      ZigZigAt transcript globalIndex requestIndex access
        requestBefore requestAfter localIndex
        stepBefore stepAfter depth) :
    Nonempty (BatchedRequestAt provenance occurrence) := by
  induction occurrence generalizing initial with
  | head head tail headTranscript tailTranscript localOccurrence =>
      cases provenance with
      | next _ _ headTransition tailTransition
          tailProvenance =>
          exact
            ⟨{
              prefixTransition :=
                RepresentedTransition.refl
                  headTransition.initial_represents
              requestInitial := initial
              prefix_final_eq := rfl
              requestTransition := headTransition
              suffixTransition := tailTransition
              events_eq := by
                simp [RepresentedTransition.refl,
                  RepresentedTransition.trans]
              final_eq := rfl
            }⟩
  | tail head tail headTranscript tailTranscript nested ih =>
      cases provenance with
      | next _ _ headTransition tailTransition
          tailProvenance =>
          obtain ⟨realized⟩ := ih tailProvenance
          exact
            ⟨{
              prefixTransition :=
                headTransition.trans realized.prefixTransition
              requestInitial := realized.requestInitial
              prefix_final_eq := realized.prefix_final_eq
              requestTransition := realized.requestTransition
              suffixTransition := realized.suffixTransition
              events_eq := by
                change
                  headTransition.events ++ tailTransition.events =
                    (headTransition.events ++
                        realized.prefixTransition.events) ++
                      realized.requestTransition.events ++
                        realized.suffixTransition.events
                rw [realized.events_eq]
                simp only [List.append_assoc]
              final_eq := realized.final_eq
            }⟩

end BatchedRequestAt


end SplaySequenceTranscript
end Splay.Accounting
