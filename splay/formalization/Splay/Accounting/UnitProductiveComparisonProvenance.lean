import Splay.Accounting.SplayExecutionProvenance
import Splay.Lazy.UnitProductiveComparisonRealizer

namespace Splay.Tree.BST.RotationExecution

open Splay.Lazy
open Splay.Rank

private theorem totalInserts_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalInserts (first ++ second) =
      Interface.totalInserts first + Interface.totalInserts second := by
  simp [Interface.totalInserts]

private theorem totalIncreases_append
    {n : ℕ} (first second : List (Interface.Operation n)) :
    Interface.totalIncreases (first ++ second) =
      Interface.totalIncreases first + Interface.totalIncreases second := by
  simp [Interface.totalIncreases]

/--
Exact comparison-rotation-execution provenance with one insert/increase bound
per concrete rotation.
-/
structure UnitProductiveComparisonProvenance
    {n : ℕ} {params : Interface.Parameters}
    (splayTree : BST 0 n)
    {length : ℕ}
    {beforeComparison afterComparison : BST 0 n}
    (execution :
      RotationExecution length beforeComparison afterComparison)
    (initial : State n) where
  transition :
    RepresentedTransition params
      (Snapshot.ofTree beforeComparison) splayTree
      (Snapshot.ofTree afterComparison) splayTree initial
  provenance :
    RepresentedComparisonTransitionProvenance
      splayTree execution transition
  totalInserts_le :
    Interface.totalInserts (eraseOperations transition.events) ≤ length
  totalIncreases_le :
    Interface.totalIncreases (eraseOperations transition.events) ≤ length

namespace UnitProductiveComparisonProvenance

/--
The concrete unit-cost one-rotation realizer composes with the standard
comparison provenance along an exact rotation execution.
-/
theorem exists_of_realizer
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : BST 0 n}
    (realizer :
      UnitProductiveComparisonRotationTraceRealizer params splayTree)
    {length : ℕ}
    {beforeComparison afterComparison : BST 0 n}
    (execution :
      RotationExecution length beforeComparison afterComparison)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (UnitProductiveComparisonProvenance
        (params := params) splayTree execution initial) := by
  induction length generalizing
      beforeComparison afterComparison initial with
  | zero =>
      cases execution
      exact
        ⟨{
          transition := RepresentedTransition.refl initialRepresents
          provenance := .refl beforeComparison initialRepresents
          totalInserts_le := by
            rfl
          totalIncreases_le := by
            rfl
        }⟩
  | succ length ih =>
      cases execution with
      | step head tail =>
          obtain ⟨headRealized⟩ :=
            realizer head initialRepresents
          obtain ⟨tailRealized⟩ :=
            ih tail headRealized.transition.final_represents
          let transition :=
            headRealized.transition.trans tailRealized.transition
          exact
            ⟨{
              transition := transition
              provenance :=
                .step head tail
                  headRealized.transition tailRealized.transition
                  tailRealized.provenance
              totalInserts_le := by
                change
                  Interface.totalInserts
                      (eraseOperations
                        (headRealized.transition.events ++
                          tailRealized.transition.events)) ≤
                    length + 1
                rw [eraseOperations_append, totalInserts_append]
                calc
                  Interface.totalInserts
                        (eraseOperations
                          headRealized.transition.events) +
                      Interface.totalInserts
                        (eraseOperations
                          tailRealized.transition.events) ≤
                      1 + length :=
                    Nat.add_le_add
                      headRealized.totalInserts_le_one
                      tailRealized.totalInserts_le
                  _ = length + 1 := by omega
              totalIncreases_le := by
                change
                  Interface.totalIncreases
                      (eraseOperations
                        (headRealized.transition.events ++
                          tailRealized.transition.events)) ≤
                    length + 1
                rw [eraseOperations_append, totalIncreases_append]
                calc
                  Interface.totalIncreases
                        (eraseOperations
                          headRealized.transition.events) +
                      Interface.totalIncreases
                        (eraseOperations
                          tailRealized.transition.events) ≤
                      1 + length :=
                    Nat.add_le_add
                      headRealized.totalIncreases_le_one
                      tailRealized.totalIncreases_le
                  _ = length + 1 := by omega
            }⟩

/-- Concrete costed provenance for every comparison rotation execution. -/
theorem exists_complete
    {n : ℕ} {params : Interface.Parameters}
    {splayTree : BST 0 n}
    {length : ℕ}
    {beforeComparison afterComparison : BST 0 n}
    (execution :
      RotationExecution length beforeComparison afterComparison)
    {initial : State n}
    (initialRepresents :
      initial.Represents params
        (Snapshot.ofTree beforeComparison) splayTree) :
    Nonempty
      (UnitProductiveComparisonProvenance
        (params := params) splayTree execution initial) :=
  exists_of_realizer
    (unitProductiveComparisonRotationTraceRealizer params splayTree)
    execution initialRepresents

end UnitProductiveComparisonProvenance

end Splay.Tree.BST.RotationExecution
