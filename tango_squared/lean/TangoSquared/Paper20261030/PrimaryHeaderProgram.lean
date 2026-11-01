import TangoSquared.Paper20261030.MultiSourceReadDispatch
import TangoSquared.Paper20261030.ExitDepthRegisters

/-! Acquiring primary component data from a reached physical record.
The bottom is an original key rank, the start is its primary path's
starting depth, and rootId names the current logical depth-tree root.
The two wing bits describe the constant-size component connector.

This controller begins after the header finger has been positioned.
Constructing the metadata, maintaining rootId across component changes,
and acquiring the initial header position are separate obligations.
-/

namespace TangoSquared.Paper20261030.PrimaryHeaderController

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

structure Header (η : Type*) where
  bottom : Int
  start : Nat
  rootId : η
  leftWing : Bool
  rightWing : Bool

variable {α ρ F σ η : Type*} [DecidableEq F]

abbrev Record (ρ η : Type*) := ρ × Option (Header η)
abbrev State (σ F ρ η : Type*) :=
  MultiSourceReadDispatch.State (Header η) (MultiSourceAugment.State σ F ρ (Option (Header η)))

def source (height : Nat) (request : Int) (component : Nat → Program σ F ρ) (header : Header η) :
    Program (MultiSourceAugment.State σ F ρ (Option (Header η))) F (Record ρ η) :=
  MultiSourceAugment.program (component (Dyadic.computeExitDepth height request header.bottom))

def initial (start : Header η → σ) (header : Header η) : MultiSourceAugment.State σ F ρ (Option (Header η)) :=
  .ready (start header)

def program (height : Nat) (request : Int) (finger : F) (start : Header η → σ) (component : Nat → Program σ F ρ) :
    Program (State σ F ρ η) F (Record ρ η) :=
  MultiSourceReadDispatch.program finger Prod.snd (initial start) (source height request component)

theorem dispatch (height : Nat) (request : Int) (finger : F) (start : Header η → σ) (component : Nat → Program σ F ρ)
    (config : Configuration F α (Record ρ η)) (position : List Bool) (current : Cursor α (Record ρ η))
    (present : config.fingers finger = some position) (reached : locate config.tree position = some current)
    (header : Header η) (stored : current.focus.rootRecord.2 = some header)
    (validRequest : Dyadic.ValidKey height request) (validBottom : Dyadic.ValidKey height header.bottom)
    {last : σ} {target : Configuration F α ρ} {reads cost}
    (run : Run (component (Dyadic.lcaDepth height request header.bottom)) (start header)
      (config.mapRecords Prod.fst) last target reads cost) :
    ∃ actualTarget actualReads actualCost,
      Run (program height request finger start component) .start config
        (.running header (.ready last)) actualTarget actualReads actualCost ∧
      actualTarget.mapRecords Prod.fst = target ∧
      actualTarget.tree.inventory Prod.snd = config.tree.inventory Prod.snd ∧ actualCost ≤ 2*cost+1 := by
  have same : Dyadic.computeExitDepth height request header.bottom = Dyadic.lcaDepth height request header.bottom :=
    (Dyadic.computeExitDepth_correct validRequest validBottom).trans (Dyadic.exitDepth_eq_lcaDepth validRequest validBottom)
  obtain ⟨actualTarget,actualReads,actualCost,actual,erases,metadata,bounded⟩ := MultiSourceAugment.compile_run run config rfl
  have selected : Run (source height request component header) (initial start header) config
      (.ready last) actualTarget actualReads actualCost := by
    simpa only [source,same,initial] using actual
  exact ⟨actualTarget,_,actualCost+1,
    MultiSourceReadDispatch.dispatch finger Prod.snd (initial start) (source height request component)
      config position current present reached header stored selected,
    erases,metadata,by omega⟩

end TangoSquared.Paper20261030.PrimaryHeaderController
