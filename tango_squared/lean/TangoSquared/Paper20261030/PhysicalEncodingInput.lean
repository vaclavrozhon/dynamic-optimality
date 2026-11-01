import TangoSquared.Paper20261030.PhysicalPortAgreement

/-! The exact component encoding used by the head kernel is the existing
complete primary representation, including its bounded virtual header. -/

namespace TangoSquared.Paper20261030.ColoredStorage

variable {α β ρ : Type*}

theorem Source.relabel_mirror (source : Source α ρ) (labels : α → β) :
    source.mirror.relabel labels = (source.relabel labels).mirror := by
  induction source <;> simp_all [Source.mirror,Source.relabel]

end TangoSquared.Paper20261030.ColoredStorage

namespace TangoSquared.Paper20261030.PackedPrimary

open ColoredStorage ProjectionLocal PreferredProjection PrimaryWings PrimaryPhysical

variable {α ρ : Type*} [DecidableEq α]

local instance encodingInputColorOrder : LinearOrder (Option Bool) :=
  inferInstanceAs (LinearOrder (WithBot Bool))

def Input.encoding {primary : PrefRouter α} (input : Input primary ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) :
    HeadBlocks.Encoding Nat (Exit α) α (Datum ρ) :=
  PackedPrimary.encoding input.start primary payload input.completeHeader

set_option backward.isDefEq.respectTransparency false in
theorem Input.encoding_tree {primary : PrefRouter α} (input : Input primary ρ)
    (payload : Exit α → Source α (List (Option (Datum ρ)))) :
    (input.encoding payload).tree Datum.record input.source = input.physical payload := by
  simp only [Input.encoding,PackedPrimary.encoding,HeadBlocks.Encoding.tree,HeadBlocks.physicalComponent,
    Input.physical,Input.completePlan,liftWing,Input.plan,PackedPrimary.plan,PackedPrimary.wing,physicalProjection,
    Bool.false_eq_true,if_false,if_true,interpret,graftWing,mirror,
    Option.map_map,Function.comp_def]
  congr 1
  congr 1
  funext source
  rw [Source.relabel_mirror]

end TangoSquared.Paper20261030.PackedPrimary
