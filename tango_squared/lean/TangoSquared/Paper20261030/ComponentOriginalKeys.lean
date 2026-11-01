import TangoSquared.Paper20261030.ComponentProjectionWords
import TangoSquared.Paper20261030.PackedPrimaryPlan

/-! The actual local component representation contains exactly the
primary tree's original ordered keys. Real depth ports are expanded by
their existing exit payloads; the virtual projection is stored at the
bottom original key. This uses the same port partition as the paper and
the earlier static primary representation, despite enriched metadata.
-/

namespace TangoSquared.Paper20261030.LocalComponentCompiler

open ColoredStorage SourcePointer Structural PhysicalForestMetadata LocalComponentForestCompiler
open PreferredProjection PrimaryWings ForestRepresentation

variable {α ρ ι η : Type*} [DecidableEq α] [DecidableEq ι] [DecidableEq η]

local instance depthPortColorOrder : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def wingOrientation : Option Bool → Bool
  | some false => true
  | _ => false

theorem port_word (start : Nat) (primary : PrefRouter α) (keys : List Nat)
    (ports : keys.filterMap (portAt start (exits primary)) = exits primary) (side : Bool) :
    (keys.filter (keepColor (PackedPrimary.color start primary) (some side))).map (PackedPrimary.label start primary) =
      (exits primary).filter (fun e => decide (e.leftOfEndpoint = side)) := by
  unfold keepColor PackedPrimary.color PackedPrimary.label
  simpa only [ports] using
    PackedPrimary.selected_word (portAt start (exits primary)) ⟨false,primary⟩ keys side

theorem payload_port_word (start : Nat) (primary : PrefRouter α) (side : Bool) (keys : List Nat)
    (selected : ∀ key ∈ keys, PackedPrimary.color start primary key = some side)
    (payload : Option Bool → Nat → Source α (List (Option (PhysicalDatum Nat ρ ι η (Option Bool)))))
    (payloadWords : ∀ key, PackedPrimary.color start primary key = some side →
      (payload (some side) key).shape.leaves = (PackedPrimary.label start primary key).subtree.leaves) :
    keys.flatMap (fun key => (payload (some side) key).shape.leaves) =
      (keys.map (PackedPrimary.label start primary)).flatMap (fun e => e.subtree.leaves) := by
  rw [List.flatMap_map]
  exact List.flatMap_congr (fun key member => payloadWords key (selected key member))

theorem original_keys (start : Nat) (primary : PrefRouter α) (decorated : Cursor Nat (η × ρ))
    (ports : decorated.tree.shape.leaves.filterMap (portAt start (exits primary)) = exits primary)
    (forest : TaggedForest (Option Bool) Nat (LocalColoredCompiler.LogicalRecord ρ η (Option Bool)) ι)
    (represented : ProjectionForest.Represents (PackedPrimary.color start primary)
      (cursor Prod.fst (PackedPrimary.color start primary) decorated) (erase forest))
    (headerKey : Nat)
    (payload : Option Bool → Nat → Source α (List (Option (PhysicalDatum Nat ρ ι η (Option Bool)))))
    (payloadWords : ∀ side key, PackedPrimary.color start primary key = some side →
      (payload (some side) key).shape.leaves = (PackedPrimary.label start primary key).subtree.leaves)
    (bottomWord : (payload none headerKey).shape.leaves = [primary.terminal])
    (config : MultiSourceProgram.Configuration (Option Bool) α (List (Option (PhysicalDatum Nat ρ ι η (Option Bool)))))
    (assembled : ForestConnector.assemble (representation none wingOrientation headerKey payload forest)
      (ForestConnector.ThreeColors.layout (representation none wingOrientation headerKey payload forest)) = some config) :
    config.tree.shape.leaves = primary.leaves := by
  let physical := representation none wingOrientation headerKey payload forest
  obtain ⟨header,present⟩ := virtual_present (C := Option Bool) none wingOrientation headerKey payload forest
  have same : config = ForestConnector.ThreeColors.configuration physical header :=
    Option.some.inj (assembled.symm.trans (ForestConnector.ThreeColors.assemble_configuration physical header present))
  rw [same,ForestConnector.ThreeColors.configuration_leaves]
  change word physical (some true) ++ header.tree.shape.leaves ++ word physical (some false) = _
  have headerWord : header.tree.shape.leaves = [primary.terminal] := by
    have actual := virtual_word (C := Option Bool) none wingOrientation headerKey payload forest
    simpa only [word,present,Option.map_some,Option.getD_some,bottomWord] using actual
  have leftWord := real_word (PackedPrimary.color start primary) decorated forest represented none (some true)
    (by decide) wingOrientation headerKey payload
  have rightWord := real_word (PackedPrimary.color start primary) decorated forest represented none (some false)
    (by decide) wingOrientation headerKey payload
  simp only [wingOrientation,Bool.false_eq_true,if_false,if_true] at leftWord rightWord
  rw [headerWord,leftWord,rightWord]
  have leftSelected : ∀ key ∈ decorated.tree.shape.leaves.filter (keepColor (PackedPrimary.color start primary) (some true)),
      PackedPrimary.color start primary key = some true := by
    intro key member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have rightSelected : ∀ key ∈ (decorated.tree.shape.leaves.filter (keepColor (PackedPrimary.color start primary) (some false))).reverse,
      PackedPrimary.color start primary key = some false := by
    intro key member
    exact of_decide_eq_true (List.mem_filter.mp (List.mem_reverse.mp member)).2
  rw [payload_port_word start primary true _ leftSelected payload (payloadWords true),
    payload_port_word start primary false _ rightSelected payload (payloadWords false),
    port_word start primary _ ports true,List.map_reverse,port_word start primary _ ports false]
  have leftFilter : (exits primary).filter (fun e => decide (e.leftOfEndpoint = true)) = (exits primary).filter (·.leftOfEndpoint) := by simp
  have rightFilter : (exits primary).filter (fun e => decide (e.leftOfEndpoint = false)) = (exits primary).filter (fun e => !e.leftOfEndpoint) := by simp
  rw [leftFilter,rightFilter]
  exact (leaf_partition primary).symm

end TangoSquared.Paper20261030.LocalComponentCompiler
