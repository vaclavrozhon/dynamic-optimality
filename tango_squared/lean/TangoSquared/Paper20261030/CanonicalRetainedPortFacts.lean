import TangoSquared.Paper20261030.CanonicalHeadWitnessOutput
import TangoSquared.Paper20261030.PackedPortAgreement

set_option autoImplicit false

/-! Retained projection ports are precisely the selected source leaves.
Disjointness and exclusion of the exchanged depth therefore follow from
the prepared source blocks, rather than separate assumptions about the
physical projections. Unchanged leaf colors also preserve the complete
canonically annotated packed block. -/

namespace TangoSquared.Paper20261030.CanonicalRetainedPortFacts

open ColoredStorage SourcePointer Structural RouterProjection RepairedPayloadLayouts

variable {α ρ ι C : Type*} [LinearOrder C]

theorem packed_ports (color : α → C) (q : C) (source : Source α ρ) :
    ports (packed color q source) = source.shape.leaves.filter (fun key => decide (color key = q)) := by
  classical
  cases present : packed color q source with
  | none =>
    have empty := packed_none_shape color q source present
    have leaves := congrArg Router.leaves empty
    change [] = source.shape.leaves.filter _
    change (source.shape.prune (fun key => decide (color key = q))).leaves = [] at leaves
    exact ((Router.leaves_prune _ _).symm.trans leaves).symm
  | some tree =>
    rw [ports,packed_shape color q source present,Router.leaves_prune]
    rfl

theorem annotated_ports (identifier : ρ → ι) (color : α → C) (q : C) (parent : Option ι) (source : Source α ρ) :
    ports (packed color q (annotate identifier color parent source)) =
      source.shape.leaves.filter (fun key => decide (color key = q)) := by
  rw [packed_ports,annotate_shape]

theorem member_source (identifier : ρ → ι) (color : α → C) (q : C) (parent : Option ι)
    (source : Source α ρ) (key : α) (member : key ∈ ports (packed color q (annotate identifier color parent source))) :
    key ∈ source.shape.leaves := by
  rw [annotated_ports] at member
  exact (List.mem_filter.mp member).1

theorem absent (identifier : ρ → ι) (color : α → C) (q : C) (parent : Option ι)
    (source : Source α ρ) (key : α) (missing : key ∉ source.shape.leaves) :
    key ∉ ports (packed color q (annotate identifier color parent source)) :=
  fun member => missing (member_source identifier color q parent source key member)

theorem separate (identifier : ρ → ι) (leftColor rightColor : α → C) (leftQ rightQ : C)
    (leftParent rightParent : Option ι) (left right : Source α ρ)
    (disjoint : ∀ key, key ∈ left.shape.leaves → key ∈ right.shape.leaves → False) :
    Separate (packed leftColor leftQ (annotate identifier leftColor leftParent left))
      (packed rightColor rightQ (annotate identifier rightColor rightParent right)) :=
  fun key hl hr => disjoint key (member_source identifier leftColor leftQ leftParent left key hl)
    (member_source identifier rightColor rightQ rightParent right key hr)

theorem annotation_color_congr (identifier : ρ → ι) (old fresh : α → C) (q : C) (parent : Option ι)
    (source : Source α ρ) (same : ∀ key ∈ source.shape.leaves, old key = fresh key) :
    packed old q (annotate identifier old parent source) = packed fresh q (annotate identifier fresh parent source) := by
  rw [annotate_color_congr identifier source parent old fresh same]
  exact packed_congr _ old fresh q (by simpa only [annotate_shape] using same)

end TangoSquared.Paper20261030.CanonicalRetainedPortFacts
