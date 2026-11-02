import ChaCha.Paper20261030.LocalComponentBoundaryRead

/-! Combining the two actual boundary observations and selecting the new
terminal colors from their stored masks. The active boundary is a real
exit, the incoming sentinel is virtual. After the switch, the old exit
becomes virtual and the incoming terminal becomes the opposite real exit.
No reference tree, desired source shape, or desired record is an input to
this calculation.
-/

namespace ChaCha.Paper20261030.Structural.HeadBoundary

open ColoredStorage SourcePointer BoundaryReadController

variable {α ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def collect {C : Type*} (active incoming : BoundaryReadController.State (Record ρ ι C)) :
    Option (Records ρ ι C) :=
  match active,incoming with
  | .done (some low) oldHigh oldTerminal,.done none incomingHigh incomingTerminal =>
    some ⟨low,oldHigh,incomingHigh,oldTerminal,incomingTerminal⟩
  | _,_ => none

theorem collect_exact {C : Type*} [LinearOrder C]
    (identifier : ρ → ι) (oldColor incomingColor : α → C)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (prefixTree oldTail incomingTail : Source α ρ) :
    collect
      (activeResult identifier oldColor low oldHigh oldTerminal depth prefixTree oldTail)
      (sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) =
      some (observed identifier oldColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
        depth prefixTree oldTail incomingTail) := rfl

def repairSwitch (identifier : ρ → ι) (records : Records ρ ι (Option Bool)) :
    Option (Records ρ ι (Option Bool)) :=
  if records.incomingTerminal.2.colors = {none} then
    if records.oldTerminal.2.colors = {some false} then repair identifier none (some true) records
    else if records.oldTerminal.2.colors = {some true} then repair identifier none (some false) records
    else none
  else none

def fromObservations (identifier : ρ → ι)
    (active incoming : BoundaryReadController.State (Record ρ ι (Option Bool))) :
    Option (Records ρ ι (Option Bool)) :=
  match collect active incoming with
  | none => none
  | some records => repairSwitch identifier records

theorem switch_observed (identifier : ρ → ι) (oldColor incomingColor : α → Option Bool)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (prefixTree oldTail incomingTail : Source α ρ) (direction : Bool)
    (oldExit : oldColor depth = some direction) (sentinel : incomingColor depth = none) :
    fromObservations identifier
      (activeResult identifier oldColor low oldHigh oldTerminal depth prefixTree oldTail)
      (sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) =
      repair identifier none (some (!direction))
        (observed identifier oldColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
          depth prefixTree oldTail incomingTail) := by
  rw [fromObservations,collect_exact]
  cases direction <;> simp only [repairSwitch,observed,fields,Source.support,oldExit,sentinel,
    Bool.not_true,Bool.not_false] <;> simp

def activeTree (records : Records ρ ι (Option Bool)) (depth : α)
    (prefixTree tail : Source α (Record ρ ι (Option Bool))) : Source α (Record ρ ι (Option Bool)) :=
  .fork records.low prefixTree (.fork records.incomingHigh (.leaf depth records.incomingTerminal) tail)

def dormantTree (records : Records ρ ι (Option Bool)) (depth : α)
    (tail : Source α (Record ρ ι (Option Bool))) : Source α (Record ρ ι (Option Bool)) :=
  .fork records.oldHigh (.leaf depth records.oldTerminal) tail

/-- Complete structural views after the switch, assembled from the five
calculated records and the three unchanged annotated blocks. This is a
correctness theorem for their values; their physical installation is a
separate local program. -/
theorem observed_views (identifier : ρ → ι) (oldColor incomingColor newColor dormantColor : α → Option Bool)
    (low oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (prefixTree oldTail incomingTail : Source α ρ) (direction : Bool)
    (oldExit : oldColor depth = some direction) (sentinel : incomingColor depth = none)
    (newExit : newColor depth = some (!direction)) (newSentinel : dormantColor depth = none)
    (prefixColors : ∀ key ∈ prefixTree.shape.leaves, oldColor key = newColor key)
    (oldColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key)
    (incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key) :
    ∃ records,
      fromObservations identifier
        (activeResult identifier oldColor low oldHigh oldTerminal depth prefixTree oldTail)
        (sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) = some records ∧
      activeTree records depth (annotate identifier oldColor (some (identifier low)) prefixTree)
        (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
        annotate identifier newColor none (.fork low prefixTree (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)) ∧
      dormantTree records depth (annotate identifier oldColor (some (identifier oldHigh)) oldTail) =
        annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail) := by
  rw [switch_observed identifier oldColor incomingColor low oldHigh incomingHigh oldTerminal incomingTerminal
    depth prefixTree oldTail incomingTail direction oldExit sentinel,← newSentinel,← newExit,
    repair_exact identifier oldColor incomingColor newColor dormantColor low oldHigh incomingHigh oldTerminal incomingTerminal
      depth prefixTree oldTail incomingTail prefixColors oldColors incomingColors]
  refine ⟨_,rfl,?_,?_⟩
  · simp only [activeTree,annotate,annotate_color_congr identifier prefixTree _ _ _ prefixColors,
      annotate_color_congr identifier incomingTail _ _ _ incomingColors]
  · simp only [dormantTree,annotate,annotate_color_congr identifier oldTail _ _ _ oldColors]

end ChaCha.Paper20261030.Structural.HeadBoundary
