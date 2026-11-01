import Splay.Lazy.CanonicalTrace
import Splay.Lazy.RankUpdate

namespace Splay.Lazy

namespace State

/--
An absorbed comparison-rank update is a complete one-event rich trace.  Its
only event is silent, and hence the exported abstract-interface trace is
empty.
-/
theorem absorbRankUpdate_trace {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (valid : state.Valid params)
    (compatible : state.RankUpdateCompatible afterView shift) :
    Trace params state [.silent]
      (state.absorbRankUpdate afterView shift) :=
  Trace.singleton (state.absorbRankUpdate_step valid compatible)

/--
The interface projection of an absorbed rank update is the empty abstract
trace between equal projected states.
-/
theorem absorbRankUpdate_interfaceTrace {n : ℕ}
    {state : State n} {afterView : HeapView n}
    {shift : Block n → ℤ} {params : Interface.Parameters}
    (valid : state.Valid params)
    (compatible : state.RankUpdateCompatible afterView shift) :
    Interface.Trace params state.toInterface []
      (state.absorbRankUpdate afterView shift).toInterface := by
  simpa [eraseOperations, Event.operations] using
    (state.absorbRankUpdate_trace valid compatible).toInterface

end State

end Splay.Lazy
