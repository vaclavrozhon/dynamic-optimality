import ChaCha.Paper20261030.ExposedHeadReassembly

/-!
# Actual packed primary components have the exposed head-switch form

An active boundary is a retained real port on exactly one side. A dormant
boundary is virtual and disappears from both physical wings. These facts,
together with the exact packing equations, give the eight-block view used
by the physical reassembly kernel. The connector lists below are computed
from the existing record-owner rule; none are discarded.
-/

namespace ChaCha.Paper20261030.HeadBlocks

open ColoredStorage ProjectionLocal PrimaryPhysical

variable {κ α β ρ τ : Type*}

local instance headExposureColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

private theorem join_none (source : Projected α ρ) : join source none = source := by
  cases source <;> rfl

private theorem none_join (source : Projected α ρ) : join none source = source := rfl

private theorem decorate_leaf (records : List ρ) (key : α) :
    decorate records (some (.leaf key [])) = some (.leaf key records) := by
  simp [decorate,Source.setRoot,Source.rootRecord]

def physicalComponent (color : κ → Option Bool) (labels : κ → α) (values : ρ → τ)
    (payload : α → Source β (List (Option τ))) (source : Source κ ρ)
    (bottom : β) (header : List τ) : Source β (List (Option τ)) :=
  component (physicalProjection color (some true) labels values payload false source)
    (physicalProjection color (some false) labels values payload true source) bottom header

def activeRecords (color : κ → Option Bool) (values : ρ → τ) (headPart tail : Source κ ρ)
    (key : κ) (low high terminal : ρ) (header : List τ) : ActiveRecords (Option τ) where
  lowerLeft := physicalConnector color (some true) values low headPart (.fork high (.leaf key terminal) tail)
  lowerRight := physicalConnector color (some false) values low headPart (.fork high (.leaf key terminal) tail)
  upperLeft := physicalConnector color (some true) values high (.leaf key terminal) tail
  upperRight := physicalConnector color (some false) values high (.leaf key terminal) tail
  bottom := header.map some
  attachment := [some (values terminal),none]

def dormantRecords (color : κ → Option Bool) (values : ρ → τ) (tail : Source κ ρ)
    (key : κ) (high terminal : ρ) (header : List τ) : DormantRecords (Option τ) where
  left := physicalConnector color (some true) values high (.leaf key terminal) tail
  right := physicalConnector color (some false) values high (.leaf key terminal) tail
  bottom := header.map some

theorem active_physical_view (color : κ → Option Bool) (labels : κ → α) (values : ρ → τ)
    (payload : α → Source β (List (Option τ))) (headPart tail : Source κ ρ)
    (key : κ) (low high terminal : ρ) (bottom : β) (header : List τ) (direction : Bool)
    (boundaryColor : color key = some direction) :
    some (physicalComponent color labels values payload
      (.fork low headPart (.fork high (.leaf key terminal) tail)) bottom header) =
    activeView
      (physicalProjection color (some true) labels values payload false headPart)
      (physicalProjection color (some false) labels values payload true headPart)
      (physicalProjection color (some true) labels values payload false tail)
      (some (.leaf bottom []))
      (physicalProjection color (some false) labels values payload true tail)
      (some (payload (labels key))) direction
      (activeRecords color values headPart tail key low high terminal header) := by
  unfold physicalComponent
  rw [component_as_join]
  simp only [physicalProjection_fork,physicalProjection_leaf,boundaryColor]
  cases direction <;>
    simp [activeView,activeRecords,join_none,none_join,decorate_leaf]

theorem dormant_physical_view (color : κ → Option Bool) (labels : κ → α) (values : ρ → τ)
    (payload : α → Source β (List (Option τ))) (tail : Source κ ρ)
    (key : κ) (high terminal : ρ) (bottom : β) (header : List τ)
    (boundaryColor : color key = none) :
    some (physicalComponent color labels values payload (.fork high (.leaf key terminal) tail) bottom header) =
    dormantView
      (physicalProjection color (some true) labels values payload false tail)
      (some (.leaf bottom []))
      (physicalProjection color (some false) labels values payload true tail)
      (dormantRecords color values tail key high terminal header) := by
  unfold physicalComponent
  rw [component_as_join]
  simp only [physicalProjection_fork,physicalProjection_leaf,boundaryColor]
  simp [dormantView,dormantRecords,join_none,none_join,decorate_leaf]

end ChaCha.Paper20261030.HeadBlocks
