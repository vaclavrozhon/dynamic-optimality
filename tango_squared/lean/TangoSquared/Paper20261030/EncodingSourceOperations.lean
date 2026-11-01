import TangoSquared.Paper20261030.PrimaryPhysicalHeadKernel

/-! Source rearrangements and boundary-payload changes in the exposed
physical encoding. The charges include every connector prefix and header
write, as well as navigation from the component root. -/

namespace TangoSquared.Paper20261030.ProjectionLocal

open ColoredStorage

variable {κ α β ρ τ C : Type*}

theorem Rearranges.decorate {before after : Projected α ρ} {budget : Nat}
    (execution : Rearranges before after budget) (records : List ρ) :
    Rearranges (decorate records before) (decorate records after) (budget+4) := by
  exact ((decorate_backward records before).trans execution |>.trans
    (decorate_forward records after)).mono (by omega)

theorem physicalProjection_rearranges [DecidableEq κ] [LinearOrder C]
    (color : κ → C) (q : C) (labels : κ → α) (values : ρ → τ)
    (payload : α → Source β (List (Option τ))) (reverse : Bool)
    {before after : Source κ ρ} {budget : Nat} (execution : SourcePointer.Rearranges before after budget) :
    Rearranges (physicalProjection color q labels values payload reverse before)
      (physicalProjection color q labels values payload reverse after) (34*budget) := by
  have packed := packed_rearranges color q execution
  cases reverse
  · simpa only [physicalProjection,interpret,Bool.false_eq_true,if_false,Option.map_map,
      Function.comp_def,← Nat.mul_assoc] using ((packed.relabel labels).mapRecords values).graft payload
  · simpa only [physicalProjection,interpret,if_true,Option.map_map,
      Function.comp_def,← Nat.mul_assoc] using ((packed.mirror.relabel labels).mapRecords values).graft payload

end TangoSquared.Paper20261030.ProjectionLocal

namespace TangoSquared.Paper20261030.HeadBlocks

open ColoredStorage ProjectionLocal PrimaryPhysical

variable {κ α β ρ τ : Type*}

local instance encodingOpsColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

set_option backward.isDefEq.respectTransparency false in
theorem Encoding.source_rearranges [DecidableEq κ] (encoding : Encoding κ α β τ) (values : ρ → τ)
    (freshHeader : List τ) {before after : Source κ ρ} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    SourcePointer.Rearranges (encoding.tree values before)
      ({encoding with header := freshHeader}.tree values after) (68*budget+12) := by
  have left := physicalProjection_rearranges encoding.color (some true) encoding.labels values encoding.payload false execution
  have right := physicalProjection_rearranges encoding.color (some false) encoding.labels values encoding.payload true execution
  have result := component_rearranges encoding.bottom encoding.header freshHeader left right
  exact result.mono (by omega)

theorem activeView_boundary_rearranges (prefixLeft prefixRight tailLeft bottom tailRight : Projected α ρ)
    {before after : Projected α ρ} (direction : Bool) (records : ActiveRecords ρ) {budget : Nat}
    (execution : Rearranges before after budget) :
    Rearranges (activeView prefixLeft prefixRight tailLeft bottom tailRight before direction records)
      (activeView prefixLeft prefixRight tailLeft bottom tailRight after direction records) (budget+20) := by
  have child := execution.decorate records.attachment
  cases direction
  · exact (((child.join_right.decorate records.upperRight).join_left.decorate records.lowerRight).join_right).mono (by omega)
  · exact ((((child.join_left.decorate records.upperLeft).join_right.decorate records.lowerLeft).join_left).join_left).mono (by omega)

end TangoSquared.Paper20261030.HeadBlocks
