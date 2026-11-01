import TangoSquared.Paper20261030.MultiSourceNestedExecution
import TangoSquared.Paper20261030.MultiSourceRecordMap
import TangoSquared.Paper20261030.ThreeColorConfiguration

set_option autoImplicit false

/-! The component header register supplies a real return route to the
new physical root. Its length is exactly the route computed from the
two wing-presence bits and at most two. This route remains valid under
an arbitrary enclosing context and with additional global fingers. -/

namespace TangoSquared.Paper20261030.NestedComponentReturn

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram MultiSourceRegisterExtension
open ForestConnector.ThreeColors

variable {α ρ ι G : Type*} [DecidableEq G]

theorem header (forest : ProjectionForest.State (Option Bool) α ρ) (header : Source α (List ρ))
    (component : Configuration (Option Bool) α (ι × List ρ))
    (erases : component.mapRecords Prod.snd = configuration forest ⟨header,[]⟩)
    (outside : List (Frame α (ι × List ρ)))
    (global : Configuration (Sum (Option Bool) G) α (ι × List ρ))
    (represented : project global = component.extend outside) :
    ∃ (focus : Source α (ι × List ρ)), ∃ inside,
      MultiSourceSingleCursor.Represents (.inl none) ⟨focus,inside++outside⟩ global ∧
      plug focus inside = component.tree ∧
      inside.length = (headerPath forest).length ∧ inside.length ≤ 2 := by
  have finger := header_finger forest ⟨header,[]⟩
  rw [← erases] at finger
  have present : component.fingers none = some (headerPath forest) := by
    simpa only [Configuration.mapRecords,address,List.reverse_nil,List.map_nil,List.append_nil] using finger
  obtain ⟨plainOutside,reached⟩ := header_atRoot forest header
  rw [← erases] at reached
  obtain ⟨current,located,_⟩ := lift_locate Prod.snd component.tree (headerPath forest) ⟨header,plainOutside⟩ reached
  have addressEq := locate_address component.tree (headerPath forest) current located
  have localRep : MultiSourceSingleCursor.Represents none current component :=
    ⟨(locate_tree located).symm,by rw [addressEq]; exact present⟩
  have count : current.ancestors.length = (headerPath forest).length := by
    simpa only [address,List.length_map,List.length_reverse] using congrArg List.length addressEq
  exact ⟨current.focus,current.ancestors,
    MultiSourceNestedExecution.position component outside global represented none current localRep,
    locate_tree located,count,count ▸ headerPath_length forest⟩

end TangoSquared.Paper20261030.NestedComponentReturn
