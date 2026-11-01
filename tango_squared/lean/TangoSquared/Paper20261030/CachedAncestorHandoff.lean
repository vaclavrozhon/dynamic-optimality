import TangoSquared.Paper20261030.EnclosingAncestorHandoff
import TangoSquared.Paper20261030.CachedAnchorHandoff

set_option autoImplicit false

/-! The parked enclosing component keeps its cache across incoming
preparation. Proper ancestry and global physical-id uniqueness derive
separation from the refreshed incoming root; it is not an extra cache
noninterference assumption. -/

namespace TangoSquared.Paper20261030.CachedRootOperation

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers MultiSourceProgram EnclosingPacketOperation

variable {α β ρ ι μ F : Type*} [DecidableEq ι] [DecidableEq F]

theorem ancestor_handoff (packet : Packet α ρ ι) (old : ι) (before after : Source β (Context.Cell α ρ ι))
    (inside outside : List (Frame β (Context.Cell α ρ ι))) (proper : inside ≠ [])
    (initial final : Configuration F β (Context.Cell α ρ ι × μ))
    (kept : RetainedMetadata Prod.fst after.rootRecord.1 initial.tree final.tree)
    (exit finger : F) (parent : Cursor β (Context.Cell α ρ ι × μ))
    (parentRep : MultiSourceSingleCursor.Represents finger parent initial)
    (parentId : parent.focus.rootRecord.1.1 = (plug before inside).rootRecord.1)
    (returned : MultiSourceSingleCursor.Represents exit (output packet old ⟨after,inside++outside⟩) (final.mapRecords Prod.fst))
    (unique : ((final.mapRecords Prod.fst).tree.inventory Prod.fst).Nodup)
    (parked : fingerLabel Prod.fst (final.mapRecords Prod.fst) finger = some (plug before inside).rootRecord.1) :
    ∃ reached : Cursor β (Context.Cell α ρ ι × μ),
      MultiSourceSingleCursor.Represents finger reached final ∧
      reached.mapRecords Prod.fst = ancestor packet old after inside outside ∧
      reached.focus.rootRecord.2 = parent.focus.rootRecord.2 := by
  obtain ⟨located,identity,different⟩ := EnclosingPacketOperation.ancestor_handoff packet old before after inside outside proper
    (final.mapRecords Prod.fst) exit finger returned unique parked
  exact retained_anchor Prod.fst after.rootRecord.1 initial final kept finger parent parentRep
    (ancestor packet old after inside outside) located (identity.trans parentId.symm) different.symm

end TangoSquared.Paper20261030.CachedRootOperation
