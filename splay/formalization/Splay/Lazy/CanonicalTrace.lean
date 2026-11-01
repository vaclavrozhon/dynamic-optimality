import Splay.Lazy.CanonicalState
import Splay.Lazy.Trace

namespace Splay.Interface

namespace Trace

/-- A single abstract-interface step is a one-operation trace. -/
theorem singleton {n : ℕ} {params : Parameters}
    {initial final : State n} {operation : Operation n}
    (step : Step params initial operation final) :
    Trace params initial [operation] final :=
  Trace.cons step (Trace.nil step.2.2)

/-- Concatenation of two compatible abstract-interface traces. -/
theorem append {n : ℕ} {params : Parameters}
    {initial middle final : State n}
    {first second : List (Operation n)}
    (firstTrace : Trace params initial first middle)
    (secondTrace : Trace params middle second final) :
    Trace params initial (first ++ second) final := by
  induction firstTrace with
  | nil _ =>
      simpa using secondTrace
  | cons head tail ih =>
      exact Trace.cons head (ih secondTrace)

end Trace

end Splay.Interface

namespace Splay.Lazy

@[simp]
theorem eraseOperations_append {n : ℕ}
    (first second : List (Event n)) :
    eraseOperations (first ++ second) =
      eraseOperations first ++ eraseOperations second := by
  simp [eraseOperations, List.flatMap_append]

namespace Trace

/-- A single rich step is a one-event rich trace. -/
theorem singleton {n : ℕ} {params : Interface.Parameters}
    {initial final : State n} {event : Event n}
    (step : Step params initial event final) :
    Trace params initial [event] final :=
  Trace.cons step (Trace.nil step.after_valid)

/-- Concatenation of two compatible rich lazy traces. -/
theorem append {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {first second : List (Event n)}
    (firstTrace : Trace params initial first middle)
    (secondTrace : Trace params middle second final) :
    Trace params initial (first ++ second) final := by
  induction firstTrace with
  | nil _ =>
      simpa using secondTrace
  | cons head tail ih =>
      exact Trace.cons head (ih secondTrace)

/--
Erasing a concatenated rich trace agrees with concatenating the two erased
abstract-interface traces.
-/
theorem toInterface_append {n : ℕ} {params : Interface.Parameters}
    {initial middle final : State n}
    {first second : List (Event n)}
    (firstTrace : Trace params initial first middle)
    (secondTrace : Trace params middle second final) :
    Interface.Trace params initial.toInterface
      (eraseOperations first ++ eraseOperations second)
      final.toInterface := by
  simpa using (firstTrace.append secondTrace).toInterface

end Trace

namespace Canonical

open Splay.Rank

/--
The canonical stable state supports the empty rich execution.  The two
numerical hypotheses are exactly those required by `canonicalState_stable`.
-/
theorem canonicalState_nilTrace {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Trace params (canonicalState snapshot tree) []
      (canonicalState snapshot tree) := by
  exact
    Trace.nil
      (canonicalState_stable
        snapshot tree params growingLimit valueBound).valid

/--
Erasing the canonical empty rich execution yields the corresponding empty
abstract-interface execution.
-/
theorem canonicalState_nilInterfaceTrace {n : ℕ}
    (snapshot : Snapshot n) (tree : Tree.BST 0 n)
    (params : Interface.Parameters)
    (growingLimit : 2 ≤ params.growingLimit)
    (valueBound :
      Analysis.contractedGap snapshot.maxRank ≤ params.valueBound) :
    Interface.Trace params
      (canonicalState snapshot tree).toInterface []
      (canonicalState snapshot tree).toInterface := by
  simpa [eraseOperations] using
    (canonicalState_nilTrace
      snapshot tree params growingLimit valueBound).toInterface

end Canonical

end Splay.Lazy
