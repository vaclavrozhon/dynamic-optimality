import ChaCha.Paper20261030.PhysicalHeadExposure

/-!
# Exchanging two actual exposed physical components

The hypotheses identify the unchanged packed routing blocks and the actual
payload at the boundary port. The conclusion is a trace on the original-key
trees, with all old and new connector/header records accounted for. Applying
this kernel to a maintained primary state also requires the exposure and
reconstruction traces and the corresponding port-agreement invariants.
-/

namespace ChaCha.Paper20261030.HeadBlocks

open ColoredStorage ProjectionLocal

variable {κ α β ρ τ : Type*}

local instance headExchangeColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

structure Encoding (κ α β τ : Type*) where
  color : κ → Option Bool
  labels : κ → α
  payload : α → Source β (List (Option τ))
  bottom : β
  header : List τ

def Encoding.wing (encoding : Encoding κ α β τ) (values : ρ → τ)
    (side : Bool) (source : Source κ ρ) : Projected β (Option τ) :=
  physicalProjection encoding.color (some side) encoding.labels values encoding.payload (!side) source

def Encoding.tree (encoding : Encoding κ α β τ) (values : ρ → τ)
    (source : Source κ ρ) : Source β (List (Option τ)) :=
  physicalComponent encoding.color encoding.labels values encoding.payload source encoding.bottom encoding.header

set_option backward.isDefEq.respectTransparency false in
theorem Encoding.active_view (encoding : Encoding κ α β τ) (values : ρ → τ)
    (headPart tail : Source κ ρ) (key : κ) (low high terminal : ρ) (direction : Bool)
    (boundary : encoding.color key = some direction) :
    some (encoding.tree values (.fork low headPart (.fork high (.leaf key terminal) tail))) =
    activeView (encoding.wing values true headPart) (encoding.wing values false headPart)
      (encoding.wing values true tail) (some (.leaf encoding.bottom []))
      (encoding.wing values false tail) (some (encoding.payload (encoding.labels key))) direction
      (activeRecords encoding.color values headPart tail key low high terminal encoding.header) :=
  active_physical_view _ _ _ _ _ _ _ _ _ _ _ _ _ boundary

set_option backward.isDefEq.respectTransparency false in
theorem Encoding.dormant_view (encoding : Encoding κ α β τ) (values : ρ → τ)
    (tail : Source κ ρ) (key : κ) (high terminal : ρ) (boundary : encoding.color key = none) :
    some (encoding.tree values (.fork high (.leaf key terminal) tail)) =
    dormantView (encoding.wing values true tail) (some (.leaf encoding.bottom []))
      (encoding.wing values false tail)
      (dormantRecords encoding.color values tail key high terminal encoding.header) :=
  dormant_physical_view _ _ _ _ _ _ _ _ _ _ boundary

theorem physical_head_exchange (oldActive newActive oldDormant incoming : Encoding κ α β τ)
    (values : ρ → τ) (headPart oldTail newTail : Source κ ρ)
    (key : κ) (low oldHigh newHigh terminal : ρ) (direction : Bool)
    (oldColor : oldActive.color key = some direction)
    (newColor : newActive.color key = some (!direction))
    (oldVirtual : oldDormant.color key = none) (newVirtual : incoming.color key = none)
    (prefixAgreement : ∀ side, oldActive.wing values side headPart = newActive.wing values side headPart)
    (oldAgreement : ∀ side, oldActive.wing values side oldTail = oldDormant.wing values side oldTail)
    (newAgreement : ∀ side, newActive.wing values side newTail = incoming.wing values side newTail)
    (oldBottom : oldActive.bottom = oldDormant.bottom)
    (newBottom : newActive.bottom = incoming.bottom)
    (oldPayload : oldActive.payload (oldActive.labels key) =
      incoming.tree values (.fork newHigh (.leaf key terminal) newTail))
    (newPayload : newActive.payload (newActive.labels key) =
      oldDormant.tree values (.fork oldHigh (.leaf key terminal) oldTail)) :
    SourcePointer.Rearranges
      (oldActive.tree values (.fork low headPart (.fork oldHigh (.leaf key terminal) oldTail)))
      (newActive.tree values (.fork low headPart (.fork newHigh (.leaf key terminal) newTail))) 288 := by
  let blocks : Fin 8 → Projected β (Option τ) := fun i => match i.val with
    | 0 => oldActive.wing values true headPart
    | 1 => oldActive.wing values true oldTail
    | 2 => some (.leaf oldActive.bottom [])
    | 3 => oldActive.wing values false oldTail
    | 4 => newActive.wing values true newTail
    | 5 => some (.leaf newActive.bottom [])
    | 6 => newActive.wing values false newTail
    | _ => oldActive.wing values false headPart
  let oldRecords := activeRecords oldActive.color values headPart oldTail key low oldHigh terminal oldActive.header
  let newRecords := activeRecords newActive.color values headPart newTail key low newHigh terminal newActive.header
  let incomingRecords := dormantRecords incoming.color values newTail key newHigh terminal incoming.header
  let oldDormantRecords := dormantRecords oldDormant.color values oldTail key oldHigh terminal oldDormant.header
  have before := oldActive.active_view values headPart oldTail key low oldHigh terminal direction oldColor
  rw [oldPayload,incoming.dormant_view values newTail key newHigh terminal newVirtual] at before
  have after := newActive.active_view values headPart newTail key low newHigh terminal (!direction) newColor
  rw [newPayload,oldDormant.dormant_view values oldTail key oldHigh terminal oldVirtual] at after
  have beforeView : some (oldActive.tree values (.fork low headPart (.fork oldHigh (.leaf key terminal) oldTail))) =
      exposedBefore blocks direction oldRecords incomingRecords := by
    simpa [exposedBefore,blocks,oldRecords,incomingRecords,
      ← newAgreement true,← newAgreement false,← newBottom] using before
  have afterView : some (newActive.tree values (.fork low headPart (.fork newHigh (.leaf key terminal) newTail))) =
      exposedAfter blocks direction newRecords oldDormantRecords := by
    simpa [exposedAfter,blocks,newRecords,oldDormantRecords,← prefixAgreement true,← prefixAgreement false,
      ← oldAgreement true,← oldAgreement false,← oldBottom] using after
  have execution := exposed_head_reassembly blocks direction oldRecords newRecords incomingRecords oldDormantRecords
  rw [← beforeView,← afterView] at execution
  exact execution

end ChaCha.Paper20261030.HeadBlocks
