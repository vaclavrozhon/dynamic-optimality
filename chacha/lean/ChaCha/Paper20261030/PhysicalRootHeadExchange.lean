import ChaCha.Paper20261030.PhysicalHeadExchange

/-! The exposed physical exchange when there is no common prefix. -/

namespace ChaCha.Paper20261030.HeadBlocks

open ColoredStorage ProjectionLocal PrimaryPhysical

variable {κ α β ρ τ : Type*}

local instance rootHeadColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def rootActiveRecords (color : κ → Option Bool) (values : ρ → τ) (tail : Source κ ρ)
    (key : κ) (high terminal : ρ) (header : List τ) : ActiveRecords (Option τ) where
  lowerLeft := []
  lowerRight := []
  upperLeft := physicalConnector color (some true) values high (.leaf key terminal) tail
  upperRight := physicalConnector color (some false) values high (.leaf key terminal) tail
  bottom := header.map some
  attachment := [some (values terminal),none]

private theorem join_none (source : Projected α ρ) : join source none = source := by
  cases source <;> rfl

private theorem none_join (source : Projected α ρ) : join none source = source := rfl

private theorem decorate_leaf (records : List ρ) (key : α) :
    decorate records (some (.leaf key [])) = some (.leaf key records) := by
  simp [decorate,Source.setRoot,Source.rootRecord]

set_option backward.isDefEq.respectTransparency false in
theorem Encoding.root_active_view (encoding : Encoding κ α β τ) (values : ρ → τ)
    (tail : Source κ ρ) (key : κ) (high terminal : ρ) (direction : Bool)
    (boundary : encoding.color key = some direction) :
    some (encoding.tree values (.fork high (.leaf key terminal) tail)) =
    activeView none none (encoding.wing values true tail) (some (.leaf encoding.bottom []))
      (encoding.wing values false tail) (some (encoding.payload (encoding.labels key))) direction
      (rootActiveRecords encoding.color values tail key high terminal encoding.header) := by
  unfold Encoding.tree physicalComponent
  rw [component_as_join]
  simp only [physicalProjection_fork,physicalProjection_leaf,boundary]
  cases direction <;>
    simp [activeView,rootActiveRecords,Encoding.wing,join_none,none_join,decorate_leaf,decorate_nil]

theorem physical_root_head_exchange (oldActive newActive oldDormant incoming : Encoding κ α β τ)
    (values : ρ → τ) (oldTail newTail : Source κ ρ)
    (key : κ) (oldHigh newHigh terminal : ρ) (direction : Bool)
    (oldColor : oldActive.color key = some direction)
    (newColor : newActive.color key = some (!direction))
    (oldVirtual : oldDormant.color key = none) (newVirtual : incoming.color key = none)
    (oldAgreement : ∀ side, oldActive.wing values side oldTail = oldDormant.wing values side oldTail)
    (newAgreement : ∀ side, newActive.wing values side newTail = incoming.wing values side newTail)
    (oldBottom : oldActive.bottom = oldDormant.bottom)
    (newBottom : newActive.bottom = incoming.bottom)
    (oldPayload : oldActive.payload (oldActive.labels key) =
      incoming.tree values (.fork newHigh (.leaf key terminal) newTail))
    (newPayload : newActive.payload (newActive.labels key) =
      oldDormant.tree values (.fork oldHigh (.leaf key terminal) oldTail)) :
    SourcePointer.Rearranges (oldActive.tree values (.fork oldHigh (.leaf key terminal) oldTail))
      (newActive.tree values (.fork newHigh (.leaf key terminal) newTail)) 288 := by
  let blocks : Fin 8 → Projected β (Option τ) := fun i => match i.val with
    | 1 => oldActive.wing values true oldTail
    | 2 => some (.leaf oldActive.bottom [])
    | 3 => oldActive.wing values false oldTail
    | 4 => newActive.wing values true newTail
    | 5 => some (.leaf newActive.bottom [])
    | 6 => newActive.wing values false newTail
    | _ => none
  let oldRecords := rootActiveRecords oldActive.color values oldTail key oldHigh terminal oldActive.header
  let newRecords := rootActiveRecords newActive.color values newTail key newHigh terminal newActive.header
  let incomingRecords := dormantRecords incoming.color values newTail key newHigh terminal incoming.header
  let oldDormantRecords := dormantRecords oldDormant.color values oldTail key oldHigh terminal oldDormant.header
  have before := oldActive.root_active_view values oldTail key oldHigh terminal direction oldColor
  rw [oldPayload,incoming.dormant_view values newTail key newHigh terminal newVirtual] at before
  have after := newActive.root_active_view values newTail key newHigh terminal (!direction) newColor
  rw [newPayload,oldDormant.dormant_view values oldTail key oldHigh terminal oldVirtual] at after
  have beforeView : some (oldActive.tree values (.fork oldHigh (.leaf key terminal) oldTail)) =
      exposedBefore blocks direction oldRecords incomingRecords := by
    simpa [exposedBefore,blocks,oldRecords,incomingRecords,
      ← newAgreement true,← newAgreement false,← newBottom] using before
  have afterView : some (newActive.tree values (.fork newHigh (.leaf key terminal) newTail)) =
      exposedAfter blocks direction newRecords oldDormantRecords := by
    simpa [exposedAfter,blocks,newRecords,oldDormantRecords,
      ← oldAgreement true,← oldAgreement false,← oldBottom] using after
  have execution := exposed_head_reassembly blocks direction oldRecords newRecords incomingRecords oldDormantRecords
  rw [← beforeView,← afterView] at execution
  exact execution

end ChaCha.Paper20261030.HeadBlocks
