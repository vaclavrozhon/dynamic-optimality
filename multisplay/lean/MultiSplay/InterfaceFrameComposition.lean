import MultiSplay.InterfaceFramedTrace

/-! # Nested component frames in the same actual history -/

namespace MultiSplay

open Splay.Interface

variable {n m k : Nat}

theorem InterfaceHistory.observable_embedded (embedding : Element n → Element m) (block : Block n) :
    InterfaceHistory.observable (InterfaceEmbedding.block embedding (InterfaceHistory.observable block)) =
      InterfaceHistory.observable (InterfaceEmbedding.block embedding block) := by
  cases mode : block.mode <;> simp [InterfaceHistory.observable, InterfaceEmbedding.block, mode]

theorem InterfacePermutation.Equivalent.prefix {a b : State n} (same : InterfacePermutation.Equivalent a b)
    (embedding : Element n → Element m) (frame : State m) :
    InterfacePermutation.Equivalent (InterfacePrefix.state embedding frame a) (InterfacePrefix.state embedding frame b) := by
  constructor
  · have perm := same.1.map (fun block => InterfaceHistory.observable (InterfaceEmbedding.block embedding block))
    simp only [List.map_map, Function.comp_def, InterfaceHistory.observable_embedded] at perm
    simpa only [InterfacePrefix.state, List.map_append, List.map_map, Function.comp_def] using
      List.Perm.append (List.Perm.refl (frame.blocks.map InterfaceHistory.observable)) perm
  · change Function.extend embedding a.value frame.value = Function.extend embedding b.value frame.value
    rw [same.2]

theorem InterfacePrefix.assoc (inner : Element n → Element m) (outer : Element m → Element k)
    (innerInj : Function.Injective inner) (outerInj : Function.Injective outer)
    (innerFrame : State m) (outerFrame : State k) (component : State n) :
    InterfacePrefix.state (outer ∘ inner) (InterfacePrefix.state outer outerFrame innerFrame) component =
      InterfacePrefix.state outer outerFrame (InterfacePrefix.state inner innerFrame component) := by
  apply congrArg₂ State.mk
  · simp [InterfacePrefix.state, List.map_append, List.map_map, Function.comp_def, InterfaceEmbedding.block, List.append_assoc]
  · funext x
    change (InterfacePrefix.state (outer ∘ inner) (InterfacePrefix.state outer outerFrame innerFrame) component).value x =
      (InterfacePrefix.state outer outerFrame (InterfacePrefix.state inner innerFrame component)).value x
    by_cases outerImage : x ∈ Set.range outer
    · obtain ⟨y, rfl⟩ := outerImage
      rw [InterfacePrefix.value_image outer outerInj]
      by_cases innerImage : y ∈ Set.range inner
      · obtain ⟨z, rfl⟩ := innerImage
        exact (InterfacePrefix.value_image (outer ∘ inner) (outerInj.comp innerInj) _ _ z).trans
          (InterfacePrefix.value_image inner innerInj _ _ z).symm
      · rw [InterfacePrefix.value_outside inner _ _ _ innerImage,
          InterfacePrefix.value_outside (outer ∘ inner) _ _ _ (by
            rintro ⟨z, same⟩
            exact innerImage ⟨z, outerInj same⟩), InterfacePrefix.value_image outer outerInj]
    · rw [InterfacePrefix.value_outside outer _ _ _ outerImage,
        InterfacePrefix.value_outside (outer ∘ inner) _ _ _ (by
          rintro ⟨z, same⟩
          exact outerImage ⟨inner z, same⟩),
        InterfacePrefix.value_outside outer _ _ _ outerImage]

namespace InterfaceFramedTrace

/-- A child selected after a split remains framed in the original global state,
including all histories outside its former parent component. -/
noncomputable def Framed.comp {params : Parameters} {component : State n} {middle : State m} {whole : State k}
    (inner : Framed params component middle) (outer : Framed params middle whole) : Framed params component whole where
  element := outer.element ∘ inner.element
  injective := outer.injective.comp inner.injective
  frame := InterfacePrefix.state outer.element outer.frame inner.frame
  passive := by
    constructor
    · intro x member z same
      rw [InterfacePrefix.allElements] at member
      rcases List.mem_append.mp member with old | small
      · exact outer.passive.elements x old (inner.element z) same
      · obtain ⟨y, selectedMem, rfl⟩ := List.mem_map.mp small
        exact inner.passive.elements y selectedMem z (outer.injective same)
    · intro block member growing z same
      rcases List.mem_append.mp member with old | small
      · exact outer.passive.creators block old growing (inner.element z) same
      · obtain ⟨original, selectedMem, rfl⟩ := List.mem_map.mp small
        exact inner.passive.creators original selectedMem growing z (outer.injective same)
  frameValid := InterfacePrefix.valid outer.element outer.injective outer.frame outer.passive outer.frameValid inner.frameValid
  equivalent := by
    rw [InterfacePrefix.assoc inner.element outer.element inner.injective outer.injective]
    have prefixed := inner.equivalent.prefix outer.element outer.frame
    exact ⟨prefixed.1.trans outer.equivalent.1, prefixed.2.trans outer.equivalent.2⟩

end InterfaceFramedTrace
end MultiSplay
