import TangoSquared.Paper20261030.LocalContextPackets
import TangoSquared.Paper20261030.HeadBlockReassembly

/-! The exposed eight-block context has fifteen connector/block-root
positions. Packet acquisition performs at most 75 local operations and
saves at most fifteen packets. These bounds are independent of block
sizes. The lengths of individual packets are still supplied invariants.
-/

namespace TangoSquared.Paper20261030.OrderedContext.PacketAcquisition

open RouterProjection ColoredStorage PacketReadController Local

variable {ι ρ : Type*}

theorem commands_length (bits : ι → Bool) (t : Source ι (List ρ)) (offset : Nat) :
    (commands bits offset (t.mapRecords List.length)).length ≤ 5*vertices t := by
  induction t generalizing offset with
  | leaf key records => cases hb : bits key <;> simp [commands,Source.mapRecords,hb,vertices]
  | fork records l r ihl ihr =>
    have leftZero := ihl 0
    have rightZero := ihr 0
    have leftDeeper := ihl (offset+records.length)
    have rightDeeper := ihr (offset+records.length)
    cases bl : present bits l.shape <;> cases br : present bits r.shape <;>
      simp only [commands,Source.mapRecords,Source.mapRecords_shape,bl,br,PacketReadController.left,
        PacketReadController.right,List.length_cons,List.length_nil,List.length_append,vertices] <;> omega

theorem packets_length (bits : ι → Bool) (t : Source ι (List ρ)) :
    (packets bits t).length ≤ vertices t := by
  induction t with
  | leaf key records => cases hb : bits key <;> simp [packets,hb,vertices]
  | fork records l r ihl ihr =>
    cases bl : present bits l.shape <;> cases br : present bits r.shape <;>
      simp only [packets,bl,br,Bool.false_or,Bool.true_or,Bool.false_eq_true,if_false,if_true,
        List.length_cons,List.length_nil,List.length_append,vertices] <;> omega

end TangoSquared.Paper20261030.OrderedContext.PacketAcquisition

namespace TangoSquared.Paper20261030.HeadBlocks.PacketAcquisition

open ColoredStorage OrderedContext

variable {ρ : Type*}

theorem before_vertices (oldRight : Bool) (records : List Bool → List ρ) :
    vertices (recordContext records [] (before oldRight)) = 15 := by
  have count := context_vertices (recordContext records [] (before oldRight))
  rw [recordContext_shape,block_count] at count
  omega

theorem acquisition_bounds (oldRight : Bool) (bits : Fin 8 → Bool) (records : List Bool → List ρ)
    (offset : Nat) :
    (OrderedContext.PacketAcquisition.commands bits offset
      ((recordContext records [] (before oldRight)).mapRecords List.length)).length ≤ 75 ∧
    (OrderedContext.PacketAcquisition.packets bits (recordContext records [] (before oldRight))).length ≤ 15 := by
  have commands := OrderedContext.PacketAcquisition.commands_length bits (recordContext records [] (before oldRight)) offset
  have packets := OrderedContext.PacketAcquisition.packets_length bits (recordContext records [] (before oldRight))
  rw [before_vertices] at commands packets
  exact ⟨commands,packets⟩

end TangoSquared.Paper20261030.HeadBlocks.PacketAcquisition
