import TangoSquared.Paper20261030.HeadBoundaryPrimaryStep

/-! The zero-depth head switch has no retained prefix and therefore
needs only four boundary records. Both records at the top of their
sources retain a null parent. Two sentinel observation tours acquire
the inputs; the terminal masks determine the new exit direction.
-/

namespace TangoSquared.Paper20261030.Structural.HeadBoundary

open ColoredStorage SourcePointer BoundaryReadController

variable {α ρ ι : Type*}

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

structure RootRecords (ρ ι : Type*) where
  oldHigh : Record ρ ι (Option Bool)
  incomingHigh : Record ρ ι (Option Bool)
  oldTerminal : Record ρ ι (Option Bool)
  incomingTerminal : Record ρ ι (Option Bool)

def collectRoots (old incoming : BoundaryReadController.State (Record ρ ι (Option Bool))) : Option (RootRecords ρ ι) :=
  match old,incoming with
  | .done none oldHigh oldTerminal,.done none incomingHigh incomingTerminal =>
    some ⟨oldHigh,incomingHigh,oldTerminal,incomingTerminal⟩
  | _,_ => none

def repairRoots (identifier : ρ → ι) (incomingColor : Option Bool) (records : RootRecords ρ ι) :
    Option (RootRecords ρ ι) :=
  match records.oldHigh.2.children,records.incomingHigh.2.children with
  | some (_,oldTail),some (_,incomingTail) =>
    let oldTerminal := terminal (identifier records.oldHigh.1) none records.oldTerminal
    let incomingTerminal := terminal (identifier records.incomingHigh.1) incomingColor records.incomingTerminal
    some ⟨branch none records.oldHigh (storedDescriptor identifier oldTerminal) oldTail,
      branch none records.incomingHigh (storedDescriptor identifier incomingTerminal) incomingTail,oldTerminal,incomingTerminal⟩
  | _,_ => none

def rootSwitch (identifier : ρ → ι) (records : RootRecords ρ ι) : Option (RootRecords ρ ι) :=
  if records.incomingTerminal.2.colors = {none} then
    if records.oldTerminal.2.colors = {some false} then repairRoots identifier (some true) records
    else if records.oldTerminal.2.colors = {some true} then repairRoots identifier (some false) records
    else none
  else none

def fromRootObservations (identifier : ρ → ι)
    (old incoming : BoundaryReadController.State (Record ρ ι (Option Bool))) : Option (RootRecords ρ ι) :=
  match collectRoots old incoming with
  | none => none
  | some records => rootSwitch identifier records

theorem root_observed_views (identifier : ρ → ι) (oldColor incomingColor newColor dormantColor : α → Option Bool)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α)
    (oldTail incomingTail : Source α ρ) (direction : Bool)
    (oldExit : oldColor depth = some direction) (sentinel : incomingColor depth = none)
    (newExit : newColor depth = some (!direction)) (newSentinel : dormantColor depth = none)
    (oldColors : ∀ key ∈ oldTail.shape.leaves, oldColor key = dormantColor key)
    (incomingColors : ∀ key ∈ incomingTail.shape.leaves, incomingColor key = newColor key) :
    ∃ records,
      fromRootObservations identifier
        (sentinelResult identifier oldColor oldHigh oldTerminal depth oldTail)
        (sentinelResult identifier incomingColor incomingHigh incomingTerminal depth incomingTail) = some records ∧
      Source.fork records.incomingHigh (.leaf depth records.incomingTerminal)
        (annotate identifier incomingColor (some (identifier incomingHigh)) incomingTail) =
        annotate identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail) ∧
      Source.fork records.oldHigh (.leaf depth records.oldTerminal)
        (annotate identifier oldColor (some (identifier oldHigh)) oldTail) =
        annotate identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail) := by
  let records : RootRecords ρ ι :=
    ⟨(oldHigh,fields identifier dormantColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)),
      (incomingHigh,fields identifier newColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)),
      (oldTerminal,fields identifier dormantColor (some (identifier oldHigh)) (.leaf depth oldTerminal)),
      (incomingTerminal,fields identifier newColor (some (identifier incomingHigh)) (.leaf depth incomingTerminal))⟩
  refine ⟨records,?_,?_,?_⟩
  · cases direction <;>
      simp [fromRootObservations,collectRoots,sentinelResult,rootSwitch,repairRoots,records,
        terminal,branch,storedDescriptor,fields,descriptor,Source.rootRecord,Source.support,
        oldExit,sentinel,newExit,newSentinel,
        oldTail.support_congr oldColor dormantColor oldColors,
        incomingTail.support_congr incomingColor newColor incomingColors]
  · simp only [records,annotate,annotate_color_congr identifier incomingTail _ _ _ incomingColors]
  · simp only [records,annotate,annotate_color_congr identifier oldTail _ _ _ oldColors]

end TangoSquared.Paper20261030.Structural.HeadBoundary

namespace TangoSquared.Paper20261030.PackedPrimary

open ColoredStorage PreferredProjection Structural

variable {α ρ ι : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

theorem root_step_boundary_views {x : α} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x 0 before after) (identifier : ρ → ι)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (oldTail incomingTail : Source Nat ρ)
    (oldDepths : ∀ key ∈ oldTail.shape.leaves, 0 < key)
    (incomingDepths : ∀ key ∈ incomingTail.shape.leaves, 0 < key) :
    ∃ (old incoming : PrefRouter α) (records : HeadBoundary.RootRecords ρ ι),
      HeadBoundary.fromRootObservations identifier
        (BoundaryReadController.sentinelResult identifier (color 0 before) oldHigh oldTerminal 0 oldTail)
        (BoundaryReadController.sentinelResult identifier (color 1 incoming) incomingHigh incomingTerminal 0 incomingTail) = some records ∧
      Source.fork records.incomingHigh (.leaf 0 records.incomingTerminal)
        (annotate identifier (color 1 incoming) (some (identifier incomingHigh)) incomingTail) =
        annotate identifier (color 0 after) none (.fork incomingHigh (.leaf 0 incomingTerminal) incomingTail) ∧
      Source.fork records.oldHigh (.leaf 0 records.oldTerminal)
        (annotate identifier (color 0 before) (some (identifier oldHigh)) oldTail) =
        annotate identifier (color 1 old) none (.fork oldHigh (.leaf 0 oldTerminal) oldTail) := by
  obtain ⟨old,incoming,direction,oldExit,sentinel,newExit,newSentinel,_,oldColors,incomingColors⟩ := head_step_colors step
  obtain ⟨records,calculated,activeExact,dormantExact⟩ :=
    HeadBoundary.root_observed_views identifier (color 0 before) (color 1 incoming) (color 0 after) (color 1 old)
      oldHigh incomingHigh oldTerminal incomingTerminal 0 oldTail incomingTail direction oldExit sentinel newExit newSentinel
      (fun key member => oldColors key (oldDepths key member))
      (fun key member => incomingColors key (incomingDepths key member))
  exact ⟨old,incoming,records,calculated,activeExact,dormantExact⟩

end TangoSquared.Paper20261030.PackedPrimary
