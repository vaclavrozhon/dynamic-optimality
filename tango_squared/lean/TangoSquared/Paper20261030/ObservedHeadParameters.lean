import TangoSquared.Paper20261030.CanonicalVirtualHeaderRead
import TangoSquared.Paper20261030.HeadPacketMarkerFree

set_option autoImplicit false

/-! Computing all finite head-exchange parameters from the five acquired
boundary records and the two acquired virtual cursors. The exit direction
is decoded from the old terminal's color mask. New logical records and
virtual headers use the existing checked computations. -/

namespace TangoSquared.Paper20261030.ObservedHeadParameters

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalPacketStaging

variable {α ρ η : Type*}

local instance observedHeadParametersColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev Physical (α ρ η : Type*) := VirtualHeadPacketController.Physical α ρ η

structure Data (α ρ η : Type*) where
  direction : Bool
  old : Records ρ η (Option Bool)
  fresh : Records ρ η (Option Bool)
  activeHeader : Physical α ρ η
  incomingHeader : Physical α ρ η
  newHeader : Physical α ρ η
  dormantHeader : Physical α ρ η

def direction (record : HeadBoundary.Record ρ η (Option Bool)) : Option Bool :=
  if record.2.colors = {some false} then some false
  else if record.2.colors = {some true} then some true else none

def compute (identifier : ρ → η)
    (active incoming : BoundaryReadController.State (HeadBoundary.Record ρ η (Option Bool)))
    (activeHeader incomingHeader : Physical α ρ η) : Option (Data α ρ η) :=
  match collect active incoming with
  | none => none
  | some old => match direction old.oldTerminal,repairSwitch identifier old with
    | some side,some fresh =>
      (VirtualHeadPacketController.exchange old fresh activeHeader incomingHeader).map
        (fun headers => ⟨side,old,fresh,activeHeader,incomingHeader,headers.1,headers.2⟩)
    | _,_ => none

def packet (stored : Physical α ρ η) : Packet α (HeadBoundary.Record ρ η (Option Bool)) Nat :=
  [some (.header stored),none]

theorem computed (identifier : ρ → η) (activeColor incomingColor : α → Option Bool)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (headPart oldTail incomingTail : Source α ρ) (side : Bool) (boundary : activeColor depth = some side)
    (fresh : Records ρ η (Option Bool))
    (repaired : fromObservations identifier
      (BoundaryReadController.activeResult identifier activeColor low oldHigh oldTerminal depth headPart oldTail)
      (BoundaryReadController.sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) = some fresh)
    (activeHeader incomingHeader newHeader dormantHeader : Physical α ρ η)
    (exchanged : VirtualHeadPacketController.exchange
      (observed identifier activeColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal depth headPart oldTail incomingTail)
      fresh activeHeader incomingHeader = some (newHeader,dormantHeader)) :
    compute identifier
      (BoundaryReadController.activeResult identifier activeColor low oldHigh oldTerminal depth headPart oldTail)
      (BoundaryReadController.sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail)
      activeHeader incomingHeader = some
        ⟨side,observed identifier activeColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
          depth headPart oldTail incomingTail,fresh,activeHeader,incomingHeader,newHeader,dormantHeader⟩ := by
  have selected : direction
      (observed identifier activeColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
        depth headPart oldTail incomingTail).oldTerminal = some side := by
    cases side <;> simp [direction,observed,fields,Source.support,boundary]
  rw [fromObservations,collect_exact] at repaired
  simp only [compute,collect_exact,selected,repaired,exchanged,Option.map_some]

end TangoSquared.Paper20261030.ObservedHeadParameters
