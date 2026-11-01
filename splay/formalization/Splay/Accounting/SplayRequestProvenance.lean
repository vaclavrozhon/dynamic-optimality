import Splay.Accounting.SplayExecutionProvenance

namespace Splay.Lazy

open Splay.Rank Splay.Tree Splay.Tree.BST

/-- A complete request is realized as one macro, allowing its two pairing
phases to span several physical splay steps. -/
def SplayRequestTraceRealizer {n : ℕ} (params : Interface.Parameters)
    (snapshot : Snapshot n) : Prop :=
  ∀ {key : ℕ} {before after : BST 0 n},
    SplayExecution key before after →
    ∀ {initial : State n}, initial.Represents params snapshot before →
      Nonempty (RepresentedTransition params snapshot before snapshot after initial)

end Splay.Lazy

namespace Splay.Tree.BST.SplaySequence

open Splay.Lazy Splay.Rank

/-- Exact composition along complete requests. Each head is a single rich
macro with the endpoints of the supplied genuine splay execution. -/
inductive RequestTransitionProvenance
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n} :
    {accesses : List (Fin n)} → {before after : BST 0 n} →
    (sequence : SplaySequence accesses before after) → {initial : State n} →
    RepresentedTransition params snapshot before snapshot after initial → Type
  | done (tree : BST 0 n) {initial : State n}
      (represented : initial.Represents params snapshot tree) :
      RequestTransitionProvenance (.done tree) (.refl represented)
  | next {access : Fin n} {accesses : List (Fin n)}
      {before middle after : BST 0 n}
      (head : SplayExecution access.val before middle)
      (tail : SplaySequence accesses middle after) {initial : State n}
      (headTransition : RepresentedTransition params snapshot before snapshot middle initial)
      (tailTransition : RepresentedTransition params snapshot middle snapshot after headTransition.final)
      (tailProvenance : RequestTransitionProvenance tail tailTransition) :
      RequestTransitionProvenance (.next head tail) (headTransition.trans tailTransition)

/-- The old rotation-level decomposition forgets to the request-level one
without changing a single rich event or either endpoint. -/
noncomputable def RepresentedTransitionProvenance.toRequest
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)} {before after : BST 0 n}
    {sequence : SplaySequence accesses before after} {initial : State n}
    {transition : RepresentedTransition params snapshot before snapshot after initial}
    (provenance : RepresentedTransitionProvenance sequence transition) :
    RequestTransitionProvenance sequence transition := by
  induction provenance with
  | done tree represented => exact .done tree represented
  | next head tail headTransition tailTransition _ _ ih =>
      exact .next head tail headTransition tailTransition ih

namespace RequestTransitionProvenance

/-- Fold request macros, sharing their actual intermediate rich states. -/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    (realizer : SplayRequestTraceRealizer params snapshot)
    {accesses : List (Fin n)} {before after : BST 0 n}
    (sequence : SplaySequence accesses before after) {initial : State n}
    (represented : initial.Represents params snapshot before) :
    Nonempty (Σ transition : RepresentedTransition params snapshot before snapshot after initial,
      RequestTransitionProvenance sequence transition) := by
  induction sequence generalizing initial with
  | done tree => exact ⟨⟨.refl represented, .done tree represented⟩⟩
  | next head tail ih =>
      obtain ⟨headTransition⟩ := realizer head represented
      obtain ⟨⟨tailTransition, provenance⟩⟩ := ih headTransition.final_represents
      exact ⟨⟨headTransition.trans tailTransition,
        .next head tail headTransition tailTransition provenance⟩⟩

/-- The list of actual event windows retains one entry for every request,
including requests whose realization emits no events. -/
def eventWindows
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)} {before after : BST 0 n}
    {sequence : SplaySequence accesses before after} {initial : State n}
    {transition : RepresentedTransition params snapshot before snapshot after initial} :
    RequestTransitionProvenance sequence transition → List (List (Event n))
  | .done _ _ => []
  | .next _ _ headTransition _ tailProvenance =>
      headTransition.events :: tailProvenance.eventWindows

@[simp] theorem eventWindows_length
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)} {before after : BST 0 n}
    {sequence : SplaySequence accesses before after} {initial : State n}
    {transition : RepresentedTransition params snapshot before snapshot after initial}
    (provenance : RequestTransitionProvenance sequence transition) :
    provenance.eventWindows.length = accesses.length := by
  induction provenance <;> simp_all [eventWindows]

@[simp] theorem eventWindows_flatten
    {n : ℕ} {params : Interface.Parameters} {snapshot : Snapshot n}
    {accesses : List (Fin n)} {before after : BST 0 n}
    {sequence : SplaySequence accesses before after} {initial : State n}
    {transition : RepresentedTransition params snapshot before snapshot after initial}
    (provenance : RequestTransitionProvenance sequence transition) :
    provenance.eventWindows.flatten = transition.events := by
  induction provenance <;> simp_all [eventWindows, RepresentedTransition.refl,
    RepresentedTransition.trans]

end RequestTransitionProvenance
end Splay.Tree.BST.SplaySequence
