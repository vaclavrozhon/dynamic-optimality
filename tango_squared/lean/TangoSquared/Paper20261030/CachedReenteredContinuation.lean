import TangoSquared.Paper20261030.CachedRootContinuation
import TangoSquared.Paper20261030.CachedReenteredComponent

set_option autoImplicit false

/-! Returning selected observations across the enclosing repair and cache
refresh. `finalData` reads only the halted scalar state of the executed
component program. The cache controller never reconstructs observations
from a mathematical representation witness. -/

namespace TangoSquared.Paper20261030.CachedReenteredContinuation

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers PrimaryHeaderController
open CachedReenteredComponent (Fingers KernelState kernel finalRoot)

variable {α β ρ ι η G σ κ : Type*} [DecidableEq G] [DecidableEq ι]

def finalData (keep : σ → κ) : KernelState σ α ρ ι G → Option κ
  | .second (some result) _ => match result.last with
    | .second _ (_, .ready last) => some (keep last)
    | _ => none
  | _ => none

def program (origin : Fingers G) (count : Nat) (hasParent : Bool)
    (source : Header η → Program σ (Option Bool) (Packet α ρ ι)) (initial : Header η → σ)
    (rootId : σ → Option η) (keep : σ → κ) :=
  CachedRootContinuation.program origin (kernel origin count hasParent source initial) (fun _ => .first .start)
    (finalRoot rootId) (fun _ => .inl none) (finalData keep)

theorem dispatch (origin : Fingers G) (count : Nat) (hasParent : Bool)
    (source : Header η → Program σ (Option Bool) (Packet α ρ ι)) (initial : Header η → σ)
    (rootId : σ → Option η) (keep : σ → κ) (header : Header η) (last : σ) (fresh : η) (known : rootId last = some fresh)
    (oldPhysical newPhysical : ι) (entryBits finalBits : Fingers G → Bool)
    (config : Configuration (Fingers G) β (Record (Context.Cell α ρ ι) η))
    (current : Cursor β (Record (Context.Cell α ρ ι) η))
    (atRoot : MultiSourceSingleCursor.Represents origin current config) (valid : WellFormed config)
    (stored : current.focus.rootRecord.2 = some header)
    (target : Configuration (Fingers G) β (Context.Cell α ρ ι)) {reads cost}
    (run : Run (kernel origin count hasParent source initial header) (.first .start) (config.mapRecords Prod.fst)
      (.second (some ⟨oldPhysical,newPhysical,.second entryBits (finalBits,.ready last)⟩) (some .done)) target reads cost)
    (returned : Cursor β (Context.Cell α ρ ι))
    (atOutput : MultiSourceSingleCursor.Represents (.inl none) returned target)
    (order : target.tree.inorderLabels Prod.fst = (config.mapRecords Prod.fst).tree.inorderLabels Prod.fst)
    (unique : (config.tree.inventory (fun record => record.1.1)).Nodup) :
    ∃ final actualReads actualCost, ∃ reached : Cursor β (Record (Context.Cell α ρ ι) η),
      Run (program origin count hasParent source initial rootId keep) (.first .start) config
        (.second (some (header,fresh,.inl none,some (keep last))) (some .done)) final actualReads actualCost ∧
      final.mapRecords Prod.fst = target ∧ reached.mapRecords Prod.fst = returned ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header fresh reached) final ∧
      (PrimaryHeaderRefresh.refreshed header fresh reached).focus.rootRecord.2 = some {header with rootId := fresh} ∧
      WellFormed final ∧
      CachedRootOperation.RetainedMetadata Prod.fst returned.focus.rootRecord.1 config.tree final.tree ∧
      actualCost ≤ 2*cost+3 :=
  CachedRootContinuation.execute_with_metadata Prod.fst origin (kernel origin count hasParent source initial) (fun _ => .first .start)
    (finalRoot rootId) (fun _ => .inl none) (finalData keep) config current atRoot valid header stored run fresh known returned atOutput order unique


end TangoSquared.Paper20261030.CachedReenteredContinuation
