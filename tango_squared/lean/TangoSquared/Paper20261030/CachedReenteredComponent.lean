import TangoSquared.Paper20261030.CachedRootOperation
import TangoSquared.Paper20261030.CachedRootMetadataAssociation
import TangoSquared.Paper20261030.ReenteredComponentExecution
import TangoSquared.Paper20261030.PrimaryComponentHeaderRefresh

set_option autoImplicit false

/-! Cached entry for the nested component controller. The actual root
read supplies both wing bits and the initial logical-root parameters.
The output logical-root id is extracted from the component's retained
scalar state and written to the reached new root. The enclosing packet
and immutable physical id stay in the preserved payload field. -/

namespace TangoSquared.Paper20261030.CachedReenteredComponent

open ColoredStorage SourcePointer MultiSourceProgram PhysicalPacketStaging PacketLayers PrimaryHeaderController

variable {α β ρ ι η G σ : Type*} [DecidableEq G] [DecidableEq ι]

abbrev Fingers (G : Type*) := Sum (Option Bool) G
abbrev BodyState (σ α ρ ι G : Type*) := MultiSourceFinish.State (ReenteredComponentExecution.EntryState G)
  ((Fingers G → Bool) × MultiSourceImmutable.State σ (Option Bool) (Packet α ρ ι) ι) (Fingers G → Bool)
abbrev KernelState (σ α ρ ι G : Type*) := MultiSourceFinish.State
  (MultiSourcePacketPrefix.State (BodyState σ α ρ ι G) α ρ ι) (Option (PacketParentRepair.State α ρ ι))
  (Option (MultiSourceEnclosingOperation.Result (BodyState σ α ρ ι G) ι))

def finalRoot (rootId : σ → Option η) : KernelState σ α ρ ι G → Option η
  | .second (some result) _ => match result.last with
    | .second _ (_, .ready last) => rootId last
    | _ => none
  | _ => none

def kernel (origin : Fingers G) (count : Nat) (hasParent : Bool)
    (source : Header η → Program σ (Option Bool) (Packet α ρ ι)) (initial : Header η → σ)
    (header : Header η) : Program (KernelState σ α ρ ι G) (Fingers G) (Context.Cell α ρ ι) :=
  ReenteredComponentExecution.program origin header.leftWing header.rightWing count
    (PrimaryHeaderRefresh.path header).length hasParent (source header) (initial header)

def program (origin : Fingers G) (count : Nat) (hasParent : Bool)
    (source : Header η → Program σ (Option Bool) (Packet α ρ ι)) (initial : Header η → σ)
    (rootId : σ → Option η) :=
  CachedRootOperation.program origin (kernel origin count hasParent source initial) (fun _ => .first .start)
    (finalRoot rootId) (fun _ => .inl none)

theorem dispatch (origin : Fingers G) (count : Nat) (hasParent : Bool)
    (source : Header η → Program σ (Option Bool) (Packet α ρ ι)) (initial : Header η → σ)
    (rootId : σ → Option η) (header : Header η) (last : σ) (fresh : η) (known : rootId last = some fresh)
    (oldPhysical newPhysical : ι) (entryBits finalBits : Fingers G → Bool)
    (config : Configuration (Fingers G) β (Record (Context.Cell α ρ ι) η))
    (current : Cursor β (Record (Context.Cell α ρ ι) η))
    (atRoot : MultiSourceSingleCursor.Represents origin current config) (valid : WellFormed config)
    (stored : current.focus.rootRecord.2 = some header)
    (target : Configuration (Fingers G) β (Context.Cell α ρ ι)) {reads cost}
    (run : Run (kernel origin count hasParent source initial header) (.first .start) (config.mapRecords Prod.fst)
      (.second (some ⟨oldPhysical,newPhysical,.second entryBits (finalBits,.ready last)⟩) (some .done)) target reads cost)
    (returned : Cursor β (Context.Cell α ρ ι))
    (atOutput : MultiSourceSingleCursor.Represents (.inl none) returned target) :
    ∃ final actualReads actualCost, ∃ reached : Cursor β (Record (Context.Cell α ρ ι) η),
      Run (program origin count hasParent source initial rootId) (.first .start) config
        (.second (some (header,fresh,.inl none)) (some .done)) final actualReads actualCost ∧
      final.mapRecords Prod.fst = target ∧ reached.mapRecords Prod.fst = returned ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header fresh reached) final ∧
      (PrimaryHeaderRefresh.refreshed header fresh reached).focus.rootRecord.2 = some {header with rootId := fresh} ∧
      WellFormed final ∧ actualCost ≤ 2*cost+3 :=
  CachedRootOperation.execute origin (kernel origin count hasParent source initial) (fun _ => .first .start)
    (finalRoot rootId) (fun _ => .inl none) config current atRoot valid header stored run fresh known returned atOutput

theorem dispatch_with_metadata (origin : Fingers G) (count : Nat) (hasParent : Bool)
    (source : Header η → Program σ (Option Bool) (Packet α ρ ι)) (initial : Header η → σ)
    (rootId : σ → Option η) (header : Header η) (last : σ) (fresh : η) (known : rootId last = some fresh)
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
      Run (program origin count hasParent source initial rootId) (.first .start) config
        (.second (some (header,fresh,.inl none)) (some .done)) final actualReads actualCost ∧
      final.mapRecords Prod.fst = target ∧ reached.mapRecords Prod.fst = returned ∧
      MultiSourceSingleCursor.Represents (.inl none) (PrimaryHeaderRefresh.refreshed header fresh reached) final ∧
      (PrimaryHeaderRefresh.refreshed header fresh reached).focus.rootRecord.2 = some {header with rootId := fresh} ∧
      WellFormed final ∧
      CachedRootOperation.RetainedMetadata Prod.fst returned.focus.rootRecord.1 config.tree final.tree ∧
      actualCost ≤ 2*cost+3 :=
  CachedRootOperation.execute_with_metadata Prod.fst origin (kernel origin count hasParent source initial) (fun _ => .first .start)
    (finalRoot rootId) (fun _ => .inl none) config current atRoot valid header stored run fresh known returned atOutput order unique

end TangoSquared.Paper20261030.CachedReenteredComponent
