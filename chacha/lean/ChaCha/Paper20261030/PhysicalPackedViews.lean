import ChaCha.Paper20261030.PhysicalContextInterpretation

/-!
# Exact physical views of exposed source forks and ports

The physical projection packs one color, optionally reverses its routing
order, and attaches the original-key payload at every retained port.
The equations below retain every connector record and attachment marker.
They apply before any bound or reassembly argument is used.
-/

namespace ChaCha.Paper20261030.ProjectionLocal

open ColoredStorage

variable {α β γ ρ τ C : Type*}

def physicalProjection [LinearOrder C] (color : α → C) (q : C)
    (labels : α → β) (values : ρ → τ) (payload : β → Source γ (List (Option τ)))
    (reverse : Bool) (source : Source α ρ) : Projected γ (Option τ) :=
  interpret payload labels values (if reverse then mirror (packed color q source) else packed color q source)

def physicalConnector [LinearOrder C] (color : α → C) (q : C) (values : ρ → τ)
    (record : ρ) (left right : Source α ρ) : List (Option τ) :=
  if owner color left right = q then [some (values record)] else []

theorem physicalProjection_fork [LinearOrder C] (color : α → C) (q : C)
    (labels : α → β) (values : ρ → τ) (payload : β → Source γ (List (Option τ)))
    (reverse : Bool) (record : ρ) (left right : Source α ρ) :
    physicalProjection color q labels values payload reverse (.fork record left right) =
      decorate (physicalConnector color q values record left right)
        (if reverse then
          join (physicalProjection color q labels values payload reverse right)
            (physicalProjection color q labels values payload reverse left)
        else
          join (physicalProjection color q labels values payload reverse left)
            (physicalProjection color q labels values payload reverse right)) := by
  cases reverse <;> by_cases owns : owner color left right = q <;>
    simp [physicalProjection,packed_fork,attach_as_decorate,owns,physicalConnector,
      mirror_decorate,mirror_join,interpret_decorate,interpret_join]

theorem physicalProjection_leaf [LinearOrder C] (color : α → C) (q : C)
    (labels : α → β) (values : ρ → τ) (payload : β → Source γ (List (Option τ)))
    (reverse : Bool) (key : α) (record : ρ) :
    physicalProjection color q labels values payload reverse (.leaf key record) =
      if color key = q then decorate [some (values record),none] (some (payload (labels key))) else none := by
  cases reverse <;> by_cases selected : color key = q <;>
    simp [physicalProjection,packed,pack,selected,Stored.toSource,mirror,Source.mirror,
      interpret,Source.relabel,Source.mapRecords,SourcePayloads.graft,decorate]

end ChaCha.Paper20261030.ProjectionLocal

namespace ChaCha.Paper20261030.PrimaryPhysical

open ColoredStorage ProjectionLocal

variable {α ρ : Type*}

theorem component_as_join (left right : Wing α ρ) (bottom : α) (header : List ρ) :
    some (component left right bottom header) =
      join (join left (some (.leaf bottom (header.map some)))) right := by
  cases left <;> cases right <;> rfl

end ChaCha.Paper20261030.PrimaryPhysical
