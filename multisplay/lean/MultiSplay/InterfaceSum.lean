import MultiSplay.InterfaceEmbedding

/-!
# Disjoint interface components in one fixed universe

Blocks are concatenated, all old data are retained, and values outside the two
embedded components are neutral. The growing-block limit is checked per actual
creator; it is not doubled when two component histories are combined.
-/

namespace MultiSplay.InterfaceSum

open Splay.Interface

variable {l r n : Nat}

noncomputable def state (left : Element l → Element n) (right : Element r → Element n)
    (a : State l) (b : State r) : State n :=
  ⟨a.blocks.map (InterfaceEmbedding.block left) ++ b.blocks.map (InterfaceEmbedding.block right),
    Function.extend left a.value (Function.extend right b.value (fun _ => 1))⟩

theorem value_left (left : Element l → Element n) (right : Element r → Element n)
    (injective : Function.Injective left) (a : State l) (b : State r) (element : Element l) :
    (state left right a b).value (left element) = a.value element :=
  injective.extend_apply _ _ _

theorem value_right (left : Element l → Element n) (right : Element r → Element n)
    (injective : Function.Injective right) (disjoint : ∀ x y, left x ≠ right y)
    (a : State l) (b : State r) (element : Element r) :
    (state left right a b).value (right element) = b.value element := by
  change Function.extend left a.value (Function.extend right b.value (fun _ => 1)) (right element) = _
  rw [Function.extend_apply' _ _ _ (by rintro ⟨x, same⟩; exact disjoint x element same), injective.extend_apply]

theorem value_outside (left : Element l → Element n) (right : Element r → Element n)
    (a : State l) (b : State r) (element : Element n)
    (outsideLeft : ¬ ∃ x, left x = element) (outsideRight : ¬ ∃ y, right y = element) :
    (state left right a b).value element = 1 := by
  change Function.extend left a.value (Function.extend right b.value (fun _ => 1)) element = 1
  rw [Function.extend_apply' _ _ _ outsideLeft, Function.extend_apply' _ _ _ outsideRight]

theorem allElements (left : Element l → Element n) (right : Element r → Element n)
    (a : State l) (b : State r) :
    (state left right a b).allElements = a.allElements.map left ++ b.allElements.map right := by
  simp [state, State.allElements, List.flatMap_append, List.flatMap_map, List.map_flatMap, InterfaceEmbedding.block]

theorem growingCount (left : Element l → Element n) (right : Element r → Element n)
    (a : State l) (b : State r) (creator : Element n) :
    (state left right a b).growingCount creator =
      (InterfaceEmbedding.state left a).growingCount creator + (InterfaceEmbedding.state right b).growingCount creator := by
  simp [state, InterfaceEmbedding.state, State.growingCount, List.filter_append]

theorem growing_left (left : Element l → Element n) (right : Element r → Element n)
    (injective : Function.Injective left) (disjoint : ∀ x y, left x ≠ right y)
    (a : State l) (b : State r) (creator : Element l) :
    (state left right a b).growingCount (left creator) = a.growingCount creator := by
  rw [growingCount, InterfaceEmbedding.growing_image left injective,
    InterfaceEmbedding.growing_outside right b (left creator)
      (by rintro ⟨y, same⟩; exact disjoint creator y same.symm), Nat.add_zero]

theorem growing_right (left : Element l → Element n) (right : Element r → Element n)
    (injective : Function.Injective right) (disjoint : ∀ x y, left x ≠ right y)
    (a : State l) (b : State r) (creator : Element r) :
    (state left right a b).growingCount (right creator) = b.growingCount creator := by
  rw [growingCount, InterfaceEmbedding.growing_image right injective,
    InterfaceEmbedding.growing_outside left a (right creator)
      (by rintro ⟨x, same⟩; exact disjoint x creator same), Nat.zero_add]

theorem growing_outside (left : Element l → Element n) (right : Element r → Element n)
    (a : State l) (b : State r) (creator : Element n)
    (outsideLeft : ¬ ∃ x, left x = creator) (outsideRight : ¬ ∃ y, right y = creator) :
    (state left right a b).growingCount creator = 0 := by
  rw [growingCount, InterfaceEmbedding.growing_outside left a creator outsideLeft,
    InterfaceEmbedding.growing_outside right b creator outsideRight]

theorem valid (left : Element l → Element n) (right : Element r → Element n)
    (leftInjective : Function.Injective left) (rightInjective : Function.Injective right)
    (disjoint : ∀ x y, left x ≠ right y) {params : Parameters}
    {a : State l} {b : State r} (aValid : a.Valid params) (bValid : b.Valid params) :
    (state left right a b).Valid params := by
  refine ⟨?_, ?_, ?_⟩
  · rw [allElements]
    refine List.nodup_append.mpr ⟨aValid.1.map leftInjective, bValid.1.map rightInjective, ?_⟩
    intro first lm second rm same
    obtain ⟨x, _, ex⟩ := List.mem_map.mp lm
    obtain ⟨y, _, ey⟩ := List.mem_map.mp rm
    exact disjoint x y (ex.trans (same.trans ey.symm))
  · intro element
    by_cases li : ∃ x, left x = element
    · obtain ⟨x, rfl⟩ := li
      simpa only [value_left left right leftInjective] using aValid.2.1 x
    · by_cases ri : ∃ y, right y = element
      · obtain ⟨y, rfl⟩ := ri
        simpa only [value_right left right rightInjective disjoint] using bValid.2.1 y
      · rw [value_outside left right a b element li ri]
        have bound := params.valueBound_ge_two
        omega
  · intro creator
    by_cases li : ∃ x, left x = creator
    · obtain ⟨x, rfl⟩ := li
      simpa only [growing_left left right leftInjective disjoint] using aValid.2.2 x
    · by_cases ri : ∃ y, right y = creator
      · obtain ⟨y, rfl⟩ := ri
        simpa only [growing_right left right rightInjective disjoint] using bValid.2.2 y
      · rw [growing_outside left right a b creator li ri]
        exact Nat.zero_le _

/-- Joining universes has no initialization surcharge: neutral slots and the
other component contribute exactly zero to each component's excess. -/
theorem excess (left : Element l → Element n) (right : Element r → Element n)
    (leftInjective : Function.Injective left) (rightInjective : Function.Injective right)
    (disjoint : ∀ x y, left x ≠ right y) (a : State l) (b : State r) :
    InterfaceForest.excess (state left right a b) = InterfaceForest.excess a + InterfaceForest.excess b := by
  have pointwise : ∀ element,
      (state left right a b).value element - 1 =
        ((InterfaceEmbedding.state left a).value element - 1) +
        ((InterfaceEmbedding.state right b).value element - 1) := by
    intro element
    by_cases li : ∃ x, left x = element
    · obtain ⟨x, rfl⟩ := li
      rw [value_left left right leftInjective, InterfaceEmbedding.value_image left leftInjective,
        InterfaceEmbedding.value_outside right b (left x)
          (by rintro ⟨y, same⟩; exact disjoint x y same.symm)]
      omega
    · by_cases ri : ∃ y, right y = element
      · obtain ⟨y, rfl⟩ := ri
        rw [value_right left right rightInjective disjoint, InterfaceEmbedding.value_image right rightInjective,
          InterfaceEmbedding.value_outside left a (right y) li]
        omega
      · rw [value_outside left right a b element li ri, InterfaceEmbedding.value_outside left a element li,
          InterfaceEmbedding.value_outside right b element ri]
  calc
    InterfaceForest.excess (state left right a b) =
        InterfaceForest.excess (InterfaceEmbedding.state left a) + InterfaceForest.excess (InterfaceEmbedding.state right b) := by
      simp only [InterfaceForest.excess, pointwise, Finset.sum_add_distrib]
    _ = _ := by rw [InterfaceEmbedding.excess left leftInjective, InterfaceEmbedding.excess right rightInjective]

end MultiSplay.InterfaceSum
