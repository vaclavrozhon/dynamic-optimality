import ChaCha.Paper20261030.HeadBoundaryObservation
import ChaCha.Paper20261030.PhysicalHeadExchange
import ChaCha.Paper20261030.LocalPackedRotationKernel
import ChaCha.Paper20261030.LocalExposedHeadReassembly

/-!
# Head-switch prefix packets computed from observed child masks

The five observed logical records contain the masks needed to determine
the owner of each exposed fork and the presence of each opaque routing
block. `active` and `dormant` compute the prefix packets of the existing
physical-view theorem from those records and the bounded stored headers.
Their definitions receive no source trees.

These are the logical singleton packets after staging. Physical packet
fields, virtual-header reconstruction, and nested attachment offsets are
handled separately; this calculation must not be confused with installing
the final physical representation.
-/

namespace ChaCha.Paper20261030.ObservedHeadBlueprint

open ColoredStorage SourcePointer Structural HeadBoundary HeadBlocks ProjectionLocal

variable {κ α β ρ ι τ C : Type*} [LinearOrder C]

theorem annotate_support (identifier : ρ → ι) (color : κ → C) (parent : Option ι) (source : Source κ ρ) :
    (annotate identifier color parent source).support color = source.support color := by
  induction source generalizing parent <;> simp_all only [annotate,Source.support]

def connector (values : Record ρ ι C → τ) (q : C) (record : Record ρ ι C) : List (Option τ) :=
  match record.2.children with
  | none => []
  | some (left,right) =>
    if PackedRotationController.ownerMask left.colors right.colors = some q then [some (values record)] else []

theorem connector_exact (color : κ → C) (values : Record ρ ι C → τ) (q : C)
    (record : Record ρ ι C) (left right : Source κ (Record ρ ι C))
    (leftChild rightChild : Child ι C)
    (children : record.2.children = some (leftChild,rightChild))
    (leftMask : leftChild.colors = left.support color) (rightMask : rightChild.colors = right.support color) :
    connector values q record = physicalConnector color q values record left right := by
  simp only [connector,children,leftMask,rightMask,PackedRotationController.ownerMask_source,
    Option.some.injEq,physicalConnector]

def owned (q : C) (record : Record ρ ι C) : List (Record ρ ι C) :=
  (connector id q record).filterMap id

theorem fork_packing (color : κ → C) (q : C)
    (record : Record ρ ι C) (left right : Source κ (Record ρ ι C))
    (leftChild rightChild : Child ι C)
    (children : record.2.children = some (leftChild,rightChild))
    (leftMask : leftChild.colors = left.support color) (rightMask : rightChild.colors = right.support color) :
    packed color q (.fork record left right) =
      decorate (owned q record) (join (packed color q left) (packed color q right)) := by
  rw [packed_fork,attach_as_decorate]
  unfold owned
  rw [connector_exact color id q record left right leftChild rightChild children leftMask rightMask]
  by_cases owns : owner color left right = q <;>
    simp only [physicalConnector,owns,if_true,if_false,decide_true,decide_false,Bool.false_eq_true,
      List.filterMap_nil,List.filterMap_cons,id_eq,Option.toList_some,List.nil_append,List.append_nil]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def active (values : Record ρ ι (Option Bool) → τ)
    (low high terminal : Record ρ ι (Option Bool)) (bottomPacket : List (Option τ)) : ActiveRecords (Option τ) where
  lowerLeft := connector values (some true) low
  lowerRight := connector values (some false) low
  upperLeft := connector values (some true) high
  upperRight := connector values (some false) high
  bottom := bottomPacket
  attachment := [some (values terminal),none]

def dormant (values : Record ρ ι (Option Bool) → τ)
    (high : Record ρ ι (Option Bool)) (bottomPacket : List (Option τ)) : DormantRecords (Option τ) where
  left := connector values (some true) high
  right := connector values (some false) high
  bottom := bottomPacket

theorem active_exact (identifier : ρ → ι) (color : κ → Option Bool)
    (values : Record ρ ι (Option Bool) → τ) (low high terminal : ρ) (key : κ)
    (headPart tail : Source κ ρ) (header : List τ) :
    let lowRecord := (low,fields identifier color none (.fork low headPart (.fork high (.leaf key terminal) tail)))
    let highRecord := (high,fields identifier color (some (identifier low)) (.fork high (.leaf key terminal) tail))
    let terminalRecord := (terminal,fields identifier color (some (identifier high)) (.leaf key terminal))
    active values lowRecord highRecord terminalRecord (header.map some) =
      activeRecords color values
        (annotate identifier color (some (identifier low)) headPart)
        (annotate identifier color (some (identifier high)) tail)
        key lowRecord highRecord terminalRecord header := by
  dsimp only
  have lowMasks := PackedRotationController.ownerMask_source color
    (annotate identifier color (some (identifier low)) headPart)
    (.fork (high,fields identifier color (some (identifier low)) (.fork high (.leaf key terminal) tail))
      (.leaf key (terminal,fields identifier color (some (identifier high)) (.leaf key terminal)))
      (annotate identifier color (some (identifier high)) tail))
  have highMasks := PackedRotationController.ownerMask_source color
    (.leaf key (terminal,fields identifier color (some (identifier high)) (.leaf key terminal)))
    (annotate identifier color (some (identifier high)) tail)
  simp only [Source.support,annotate_support] at lowMasks highMasks
  simp only [active,activeRecords,connector,fields,descriptor,Source.support,physicalConnector]
  rw [lowMasks,highMasks]
  simp only [Option.some.injEq,fields,descriptor,Source.support]
  rfl

theorem dormant_exact (identifier : ρ → ι) (color : κ → Option Bool)
    (values : Record ρ ι (Option Bool) → τ) (high terminal : ρ) (key : κ)
    (tail : Source κ ρ) (header : List τ) :
    let highRecord := (high,fields identifier color none (.fork high (.leaf key terminal) tail))
    let terminalRecord := (terminal,fields identifier color (some (identifier high)) (.leaf key terminal))
    dormant values highRecord (header.map some) = dormantRecords color values
      (annotate identifier color (some (identifier high)) tail) key highRecord terminalRecord header := by
  dsimp only
  have masks := PackedRotationController.ownerMask_source color
    (.leaf key (terminal,fields identifier color (some (identifier high)) (.leaf key terminal)))
    (annotate identifier color (some (identifier high)) tail)
  simp only [Source.support,annotate_support] at masks
  simp only [dormant,dormantRecords,connector,fields,descriptor,Source.support,physicalConnector]
  rw [masks]
  simp only [Option.some.injEq,fields,descriptor,Source.support]
  rfl

def childPresent (q : C) (right : Bool) (record : Record ρ ι C) : Bool :=
  match record.2.children with
  | none => false
  | some (leftChild,rightChild) => decide (q ∈ (if right then rightChild else leftChild).colors)

theorem child_present [DecidableEq κ] (identifier : ρ → ι) (color : κ → C) (q : C)
    (parent : Option ι) (record : ρ) (left right : Source κ ρ) (side : Bool) :
    childPresent q side (record,fields identifier color parent (.fork record left right)) =
      (packed color q (if side then right else left)).isSome := by
  cases side <;> simp only [childPresent,fields,descriptor,Bool.false_eq_true,if_false,if_true,
    PackedRotationController.packed_isSome]

theorem physical_present [DecidableEq κ] (color : κ → C) (q : C) (labels : κ → α) (values : ρ → τ)
    (payload : α → Source β (List (Option τ))) (reverse : Bool) (source : Source κ ρ) :
    (physicalProjection color q labels values payload reverse source).isSome = decide (q ∈ source.support color) := by
  unfold physicalProjection interpret
  rw [Option.isSome_map]
  cases reverse <;> simp only [Bool.false_eq_true,if_false,if_true]
  · exact PackedRotationController.packed_isSome color q source
  · cases equal : packed color q source <;>
      simpa only [equal,mirror,Option.map_none,Option.map_some,Option.isSome_some,Option.isSome_none] using
        (PackedRotationController.packed_isSome color q source)

def bits (records : Records ρ ι (Option Bool)) (key : Fin 8) : Bool :=
  match key.val with
  | 0 => childPresent (some true) false records.low
  | 1 => childPresent (some true) true records.oldHigh
  | 2 => true
  | 3 => childPresent (some false) true records.oldHigh
  | 4 => childPresent (some true) true records.incomingHigh
  | 5 => true
  | 6 => childPresent (some false) true records.incomingHigh
  | _ => childPresent (some false) false records.low

def blocks (old incoming : Encoding κ α β τ) (values : ρ → τ)
    (headPart oldTail incomingTail : Source κ ρ) (key : Fin 8) : Projected β (Option τ) :=
  match key.val with
  | 0 => old.wing values true headPart
  | 1 => old.wing values true oldTail
  | 2 => some (.leaf old.bottom [])
  | 3 => old.wing values false oldTail
  | 4 => incoming.wing values true incomingTail
  | 5 => some (.leaf incoming.bottom [])
  | 6 => incoming.wing values false incomingTail
  | _ => old.wing values false headPart

theorem bits_exact [DecidableEq κ] (identifier : ρ → ι) (old incoming : Encoding κ α β τ)
    (values : Record ρ ι (Option Bool) → τ)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : κ)
    (headPart oldTail incomingTail : Source κ ρ) :
    let records := observed identifier old.color incoming.color low oldHigh incomingHigh oldTerminal incomingTerminal
      depth headPart oldTail incomingTail
    ∀ key, bits records key = (blocks old incoming values
      (annotate identifier old.color (some (identifier low)) headPart)
      (annotate identifier old.color (some (identifier oldHigh)) oldTail)
      (annotate identifier incoming.color (some (identifier incomingHigh)) incomingTail) key).isSome := by
  dsimp only
  intro key
  fin_cases key <;> simp only [bits,blocks,observed,childPresent,fields,descriptor,
    Bool.false_eq_true,if_false,if_true,Encoding.wing,physical_present,annotate_support,Option.isSome_some]

def beforeContext (values : Record ρ ι (Option Bool) → τ) (direction : Bool)
    (records : Records ρ ι (Option Bool)) (activeHeader incomingHeader : List (Option τ)) :
    Source (Fin 8) (List (Option τ)) :=
  ExposedLocal.beforeContext direction (active values records.low records.oldHigh records.oldTerminal activeHeader)
    (dormant values records.incomingHigh incomingHeader)

def afterContext (values : Record ρ ι (Option Bool) → τ) (direction : Bool)
    (records : Records ρ ι (Option Bool)) (activeHeader dormantHeader : List (Option τ)) :
    Source (Fin 8) (List (Option τ)) :=
  ExposedLocal.afterContext direction (active values records.low records.incomingHigh records.incomingTerminal activeHeader)
    (dormant values records.oldHigh dormantHeader)

theorem block_order (values : Record ρ ι (Option Bool) → τ) (direction : Bool)
    (before after : Records ρ ι (Option Bool)) (oldHeader incomingHeader newHeader dormantHeader : List (Option τ)) :
    (beforeContext values direction before oldHeader incomingHeader).shape.leaves =
      (afterContext values direction after newHeader dormantHeader).shape.leaves := by
  simp only [beforeContext,afterContext,ExposedLocal.before_shape,ExposedLocal.after_shape]
  exact HeadBlocks.block_order direction

theorem block_count (values : Record ρ ι (Option Bool) → τ) (direction : Bool)
    (records : Records ρ ι (Option Bool)) (activeHeader incomingHeader : List (Option τ)) :
    (beforeContext values direction records activeHeader incomingHeader).shape.leaves.length = 8 := by
  simp only [beforeContext,ExposedLocal.before_shape]
  exact HeadBlocks.block_count direction

end ChaCha.Paper20261030.ObservedHeadBlueprint
