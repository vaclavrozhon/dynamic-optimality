import ChaCha.Paper20261030.ObservedHeadParameters
import ChaCha.Paper20261030.RootMixedHeadExchange

set_option autoImplicit false

/-! The minimum-depth exchange computes its parameters from four boundary
records and two virtual cursors. The empty prefix in `lift` is only an
encoding for the common exchange interface: it allocates no source node
and contributes no physical packet. -/

namespace ChaCha.Paper20261030.ObservedRootHeadParameters

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalPacketStaging

variable {α ρ η : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def observed (identifier : ρ → η) (activeColor incomingColor : α → Option Bool)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (oldTail incomingTail : Source α ρ) : RootRecords ρ η :=
  ⟨(oldHigh,fields identifier activeColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)),
    (incomingHigh,fields identifier incomingColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)),
    (oldTerminal,fields identifier activeColor (some (identifier oldHigh)) (.leaf depth oldTerminal)),
    (incomingTerminal,fields identifier incomingColor (some (identifier incomingHigh)) (.leaf depth incomingTerminal))⟩

theorem collect_exact (identifier : ρ → η) (activeColor incomingColor : α → Option Bool)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (oldTail incomingTail : Source α ρ) :
    collectRoots
      (BoundaryReadController.sentinelResult identifier activeColor oldHigh oldTerminal depth oldTail)
      (BoundaryReadController.sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) =
      some (observed identifier activeColor incomingColor oldHigh incomingHigh oldTerminal incomingTerminal
        depth oldTail incomingTail) := rfl

def compute (identifier : ρ → η)
    (active incoming : BoundaryReadController.State (HeadBoundary.Record ρ η (Option Bool)))
    (activeHeader incomingHeader : ObservedHeadParameters.Physical α ρ η) :
    Option (ObservedHeadParameters.Data α ρ η) :=
  match collectRoots active incoming with
  | none => none
  | some old => match ObservedHeadParameters.direction old.oldTerminal,rootSwitch identifier old with
    | some side,some fresh =>
      (VirtualHeadPacketController.exchangeRoot old fresh activeHeader incomingHeader).map
        (fun headers => ⟨side,RootMixedHeadExchange.lift old,RootMixedHeadExchange.lift fresh,
          activeHeader,incomingHeader,headers.1,headers.2⟩)
    | _,_ => none

theorem computed (identifier : ρ → η) (activeColor incomingColor : α → Option Bool)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (oldTail incomingTail : Source α ρ) (side : Bool) (boundary : activeColor depth = some side)
    (fresh : RootRecords ρ η)
    (repaired : fromRootObservations identifier
      (BoundaryReadController.sentinelResult identifier activeColor oldHigh oldTerminal depth oldTail)
      (BoundaryReadController.sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) = some fresh)
    (activeHeader incomingHeader newHeader dormantHeader : ObservedHeadParameters.Physical α ρ η)
    (exchanged : VirtualHeadPacketController.exchangeRoot
      (observed identifier activeColor incomingColor oldHigh incomingHigh oldTerminal incomingTerminal depth oldTail incomingTail)
      fresh activeHeader incomingHeader = some (newHeader,dormantHeader)) :
    compute identifier
      (BoundaryReadController.sentinelResult identifier activeColor oldHigh oldTerminal depth oldTail)
      (BoundaryReadController.sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail)
      activeHeader incomingHeader = some
        ⟨side,RootMixedHeadExchange.lift (observed identifier activeColor incomingColor
          oldHigh incomingHigh oldTerminal incomingTerminal depth oldTail incomingTail),
          RootMixedHeadExchange.lift fresh,activeHeader,incomingHeader,newHeader,dormantHeader⟩ := by
  have selected : ObservedHeadParameters.direction
      (observed identifier activeColor incomingColor oldHigh incomingHigh oldTerminal incomingTerminal
        depth oldTail incomingTail).oldTerminal = some side := by
    cases side <;> simp [ObservedHeadParameters.direction,observed,fields,Source.support,boundary]
  rw [fromRootObservations,collect_exact] at repaired
  simp only [compute,collect_exact,selected,repaired,exchanged,Option.map_some]

end ChaCha.Paper20261030.ObservedRootHeadParameters
