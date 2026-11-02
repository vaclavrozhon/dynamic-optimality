import ChaCha.Paper20261030.CanonicalRepairedRouting

set_option autoImplicit false

/-! Canonical routing depends on payloads only at its actual port leaves.
Disjoint port sets therefore allow independently reconstructed pieces to
be combined into one payload map. All functions and tagged trees here
are representation witnesses, not runtime controller inputs. -/

namespace ChaCha.Paper20261030.CanonicalPacketLayerViews

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {α β ρ ι : Type*}

theorem routing_payload_congr (first last : α → Source β (Packet α ρ ι))
    (reverse : Bool) (parent : Option ι) (tagged : Tagged α ρ ι)
    (same : ∀ key ∈ tagged.shape.leaves, first key = last key) :
    routing first reverse parent tagged = routing last reverse parent tagged := by
  induction tagged generalizing parent with
  | leaf key record =>
    rw [leaf,leaf,same key (by simp only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton])]
  | fork record left right ihl ihr =>
    have hl := ihl (some record.1) (fun key member => same key (List.mem_append_left _ member))
    have hr := ihr (some record.1) (fun key member => same key (List.mem_append_right _ member))
    rw [fork,fork]
    cases reverse <;> simp only [Bool.false_eq_true,if_false,if_true,hl,hr]

end ChaCha.Paper20261030.CanonicalPacketLayerViews
