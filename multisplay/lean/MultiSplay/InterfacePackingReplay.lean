import MultiSplay.InterfacePacking

/-! # Executing any selected packed component while retaining every other one -/

namespace MultiSplay.InterfacePacking

open Splay.Interface

variable {m : Nat} {params : Parameters}

def Component.withSource (component : Component m) (source : State component.size) : Component m :=
  {component with source := source}

theorem separate_withSource (head : Component m) (front back : List (Component m))
    (separate : (front ++ head :: back).Pairwise Component.Disjoint) (source : State head.size) :
    (front ++ head.withSource source :: back).Pairwise Component.Disjoint := by
  simpa [List.pairwise_append, List.pairwise_cons, Component.Disjoint, Component.withSource] using separate

/-- The old global state is arbitrary up to observable history equality.
The next state is an actual strict execution with the same local charges,
and its complete packing retains every other component and the archive. -/
theorem replay (archive : State m) (head : Component m) (front back : List (Component m))
    (archiveValid : archive.Valid params) (separate : (front ++ head :: back).Pairwise Component.Disjoint)
    (sources : ∀ component ∈ front ++ back, component.source.Valid params)
    (passive : ∀ component ∈ front ++ head :: back, InterfacePrefix.Passive component.element archive)
    (whole : State m) (represented : InterfacePermutation.Equivalent (pack archive (front ++ head :: back)) whole)
    {after : State head.size} {word : List (Operation head.size)} (execution : Trace params head.source word after) :
    ∃ translated final, Trace params whole translated final ∧
      InterfacePermutation.Equivalent (pack archive (front ++ head.withSource after :: back)) final ∧
      translated.length = word.length ∧ totalActivity translated = totalActivity word ∧
      totalInserts translated = totalInserts word ∧ totalIncreases translated = totalIncreases word ∧
      totalDecreases translated = totalDecreases word := by
  let selected := componentFrame archive head front back archiveValid separate sources passive
  let framed : InterfaceFramedTrace.Framed params head.source whole :=
    {selected with equivalent := ⟨selected.equivalent.1.trans represented.1, selected.equivalent.2.trans represented.2⟩}
  obtain ⟨translated, final, actual, ⟨next, elementEq, frameEq⟩, length, activity, inserts, increases, decreases⟩ := framed.trace execution
  have nextEq := next.equivalent
  rw [elementEq, frameEq] at nextEq
  change InterfacePermutation.Equivalent (pack archive (head.withSource after :: (front ++ back))) final at nextEq
  have order : (front ++ head.withSource after :: back).Perm (head.withSource after :: (front ++ back)) := List.perm_middle
  have reorder := perm archive order (separate_withSource head front back separate after)
  exact ⟨translated, final, actual, ⟨reorder.1.trans nextEq.1, reorder.2.trans nextEq.2⟩,
    length, activity, inserts, increases, decreases⟩

end MultiSplay.InterfacePacking
