import MultiSplay.InterfacePackingRegion

/-! # The initial potential depends on active components, not reserved space -/

namespace MultiSplay.InterfacePacking

open Splay.Interface
open InterfaceForest (excess)

variable {n m : Nat}

theorem prefix_excess (element : Element n → Element m) (injective : Function.Injective element)
    (frame : State m) (source : State n) :
    excess (InterfacePrefix.state element frame source) ≤ excess frame + excess source := by
  rw [← InterfaceEmbedding.excess element injective source]
  unfold excess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases inside : x ∈ Set.range element
  · obtain ⟨y, rfl⟩ := inside
    rw [InterfacePrefix.value_image element injective, InterfaceEmbedding.value_image element injective]
    omega
  · rw [InterfacePrefix.value_outside element _ _ _ inside, InterfaceEmbedding.value_outside element _ _ inside]
    omega

theorem pack_excess (archive : State m) (components : List (Component m)) :
    excess (pack archive components) ≤ excess archive + (components.map (fun component => excess component.source)).sum := by
  induction components with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      have paid := prefix_excess head.element head.injective (pack archive tail) head.source
      simp only [List.map_cons, List.sum_cons, pack]
      omega

theorem pack_empty_blocks (archive : State m) (components : List (Component m))
    (empty : archive.blocks = []) (sources : ∀ component ∈ components, component.source.blocks = []) :
    (pack archive components).blocks = [] := by
  induction components with
  | nil => exact empty
  | cons head tail ih =>
      change (pack archive tail).blocks ++ head.source.blocks.map _ = []
      rw [ih (fun component member => sources component (List.mem_cons_of_mem _ member)), sources head (List.mem_cons_self)]
      rfl

end MultiSplay.InterfacePacking
