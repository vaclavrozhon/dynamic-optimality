import TangoSquared.Paper20261030.CachedReenteredContinuation
import TangoSquared.Paper20261030.ComponentBoundaryContinuation

set_option autoImplicit false

/-! Cache-driven preparation followed by boundary reads. The continuation
retains the observer's actual scalar result, containing at most three
logical records, across the final cache refresh. -/

namespace TangoSquared.Paper20261030.CachedObservedComponent

open ColoredStorage SourcePointer PhysicalForestMetadata LocalComponentForestCompiler
open ForestConnector.ThreeColors PrimaryHeaderController

variable {α ρ ι η G σ : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η] [DecidableEq G]

local instance cachedObservedColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

abbrev State (σ α ρ ι η : Type*) := MultiSourceFinish.State
  (LocalComponentForestCompiler.State σ α ρ ι η (Option Bool))
  (ComponentBoundaryReadController.State α ρ ι η (Option Bool)) η

def rootId : State σ α ρ ι η → Option η
  | .second _ (.ready (.ready (.ready _ ident))) => some ident
  | _ => none

def observations : State σ α ρ ι η → BoundaryReadController.State (LocalColoredCompiler.LogicalRecord ρ η (Option Bool))
  | .second _ (.ready (.ready (.ready values _))) => values
  | _ => .start

def program (entry : Sum (Option Bool) G) (count : Nat) (hasParent prefixPresent : Bool)
    (source : Header η → SourceLocalProgram.Program σ ρ) (initial : Header η → σ) :=
  CachedReenteredContinuation.program entry count hasParent
    (fun header => ComponentBoundaryContinuation.program (α := α) (ι := ι) (source header) prefixPresent header.rootId)
    (fun header => ComponentBoundaryContinuation.initial (source header) prefixPresent header.rootId (initial header))
    rootId observations

theorem rootId_ready (parameter ident : η) (values : BoundaryReadController.State (LocalColoredCompiler.LogicalRecord ρ η (Option Bool))) :
    rootId (σ := σ) (.second parameter (ComponentObserverCompiler.ready (α := α) (ι := ι) values ident)) = some ident := rfl

theorem observations_ready (parameter ident : η) (values : BoundaryReadController.State (LocalColoredCompiler.LogicalRecord ρ η (Option Bool))) :
    observations (σ := σ) (.second parameter (ComponentObserverCompiler.ready (α := α) (ι := ι) values ident)) = values := rfl

theorem working_records (state : State σ α ρ ι η) :
    BoundaryReadController.workingRecords (observations state) ≤ 3 := BoundaryReadController.working_records _

end TangoSquared.Paper20261030.CachedObservedComponent
