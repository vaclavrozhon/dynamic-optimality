import TangoSquared.Paper20261030.RoutingUniquePort

set_option autoImplicit false

/-! Distinct original keys imply distinct opaque routing ports: every
payload is a nonempty binary tree, so repeating a port would repeat an
original leaf. This supplies routing-leaf uniqueness from the actual
shared representation rather than an additional depth-source premise. -/

namespace TangoSquared.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer

variable {α β ρ : Type*}

private theorem leaves_nonempty {δ : Type*} (source : Source β δ) : ∃ key, key ∈ source.shape.leaves := by
  induction source with
  | leaf key record => exact ⟨key,by simp [Source.shape,RouterProjection.Router.leaves]⟩
  | fork record left right ihl _ =>
    obtain ⟨key,member⟩ := ihl
    exact ⟨key,List.mem_append_left _ member⟩

theorem keys_nodup_of_flatMap (word : α → List β) (keys : List α)
    (nonempty : ∀ key ∈ keys, ∃ value, value ∈ word key) (distinct : (keys.flatMap word).Nodup) : keys.Nodup := by
  induction keys with
  | nil => exact List.nodup_nil
  | cons key rest ih =>
    have parts := List.nodup_append'.mp distinct
    apply List.nodup_cons.mpr
    constructor
    · intro repeated
      obtain ⟨value,member⟩ := nonempty key (List.mem_cons_self)
      exact (List.disjoint_left.mp parts.2.2) member (List.mem_flatMap.mpr ⟨key,repeated,member⟩)
    · exact ih (fun other member => nonempty other (List.mem_cons_of_mem _ member)) parts.2.1

theorem graft_distinct (payload : α → Source β (List (Option ρ))) (source : Source α (List ρ))
    (distinct : (graft payload source).shape.leaves.Nodup) : source.shape.leaves.Nodup := by
  rw [graft_leaves] at distinct
  exact keys_nodup_of_flatMap (fun key => (payload key).shape.leaves) source.shape.leaves
    (fun key _ => leaves_nonempty (payload key)) distinct

end TangoSquared.Paper20261030.SourcePayloads

namespace TangoSquared.Paper20261030.CanonicalPacketLayerViews

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

theorem routing_keys_distinct (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (tagged : Tagged α ρ ι) (distinct : (routing payload reverse parent tagged).shape.leaves.Nodup) :
    tagged.shape.leaves.Nodup := by
  have unique := SourcePayloads.graft_distinct payload _ distinct
  cases reverse <;> simpa only [Bool.false_eq_true,if_false,if_true,Source.mapRecords_shape,
    Source.mirror_leaves,annotate_shape,List.nodup_reverse] using unique

end TangoSquared.Paper20261030.CanonicalPacketLayerViews
