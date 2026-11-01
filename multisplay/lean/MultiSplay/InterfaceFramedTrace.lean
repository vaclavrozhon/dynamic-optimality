import MultiSplay.InterfacePrefixTrace
import MultiSplay.InterfacePermutation

/-!
# Local traces in an arbitrary shared persistent history

`Framed` describes an existing component and its passive records in the actual
global state. The records may be interleaved arbitrarily. A whole local trace
is realized globally with identical charges, retaining the passive frame and
the same component embedding. No new initialization is performed.
-/

namespace MultiSplay.InterfaceFramedTrace

open Splay.Interface

variable {n m : Nat}

structure Framed (params : Parameters) (component : State n) (whole : State m) where
  element : Element n → Element m
  injective : Function.Injective element
  frame : State m
  passive : InterfacePrefix.Passive element frame
  frameValid : frame.Valid params
  equivalent : InterfacePermutation.Equivalent (InterfacePrefix.state element frame component) whole

theorem Framed.valid {params : Parameters} {component : State n} {whole : State m}
    (framed : Framed params component whole) (valid : component.Valid params) : whole.Valid params :=
  framed.equivalent.valid (InterfacePrefix.valid framed.element framed.injective framed.frame framed.passive framed.frameValid valid)

/-- One actual global execution with precisely the local accounting charges.
The output retains the same passive history, including immutable creators. -/
theorem Framed.trace {params : Parameters} {before after : State n} {whole : State m}
    (framed : Framed params before whole) {word : List (Operation n)}
    (execution : Trace params before word after) :
    ∃ translated final, Trace params whole translated final ∧
      (∃ next : Framed params after final, next.element = framed.element ∧ next.frame = framed.frame) ∧
      translated.length = word.length ∧ totalActivity translated = totalActivity word ∧
      totalInserts translated = totalInserts word ∧ totalIncreases translated = totalIncreases word ∧
      totalDecreases translated = totalDecreases word := by
  have prefixed := InterfacePrefix.trace framed.element framed.injective framed.frame framed.passive framed.frameValid execution
  obtain ⟨translated, final, actual, same, length, activity, inserts, increases, decreases⟩ :=
    InterfacePermutation.trace framed.equivalent prefixed
  refine ⟨translated, final, actual, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨framed.element, framed.injective, framed.frame, framed.passive, framed.frameValid, same⟩, rfl, rfl⟩
  · simpa using length
  · simpa using activity
  · simpa using inserts
  · simpa using increases
  · simpa using decreases

end MultiSplay.InterfaceFramedTrace
