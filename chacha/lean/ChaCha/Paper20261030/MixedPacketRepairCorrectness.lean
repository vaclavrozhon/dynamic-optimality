import ChaCha.Paper20261030.HeadPacketRepairPlan

set_option autoImplicit false

/-!
# The repaired physical fields equal the actual planned neighbors

`Recognizes` checks that each planned real layer exists and each raw
offset is within the packet. Repacking establishes it from the layer
agreement and ordinary residual roots. `Correct` then states exact
parent/child fields at every repaired layer. Fork child ids come from
the reached physical children, reordered by the wing orientation.
-/

namespace ChaCha.Paper20261030.MixedPacketRepair

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers

variable {κ α β ρ ι : Type*}

def Recognizes : Layers → Packet α ρ ι → Prop
  | .base,_ => True
  | .raw count rest,packet => count ≤ packet.length ∧ Recognizes rest (packet.drop count)
  | .leaf rest,some (.real _) :: tail => Recognizes rest tail
  | .fork _,some (.real _) :: _ => True
  | .prefix,some (.real _) :: _ => True
  | _,_ => False

def Correct : Layers → Option ι → Option (ι × ι) → Packet α ρ ι → Prop
  | .base,_,_,_ => True
  | .raw count rest,parent,children,packet => count ≤ packet.length ∧ Correct rest parent children (packet.drop count)
  | .leaf rest,parent,children,some (.real (_,fields)) :: tail =>
      fields = neighbors parent false none ∧ Correct rest none children tail
  | .fork reverse,parent,children,some (.real (_,fields)) :: _ => fields = neighbors parent reverse children
  | .prefix,parent,_,some (.real (_,fields)) :: _ => fields.parent = parent
  | _,_,_,_ => False

theorem recognizes_rebuilt (vertexId : ι) (base : Packet α ρ ι) {plan : Layers} {expression : Expression α ρ ι}
    (same : Matches plan expression) (ready : Ready base expression) : Recognizes plan (rebuilt vertexId base expression) := by
  induction same with
  | base => trivial
  | raw records plan expression same ih =>
    simp only [rebuilt,Recognizes,List.length_append,List.drop_left]
    exact ⟨Nat.le_add_right _ _,ih ready⟩
  | leaf id records fields plan expression same ih => exact ih ready
  | fork => trivial
  | «prefix» records =>
    obtain ⟨id,tail,fields,rest,equal⟩ := ready
    rw [rebuilt,equal]
    trivial

theorem edit_correct (plan : Layers) (parent : Option ι) (children : Option (ι × ι))
    (packet : Packet α ρ ι) (recognized : Recognizes plan packet) : Correct plan parent children (edit plan parent children packet) := by
  induction plan generalizing parent packet with
  | base => trivial
  | raw count rest ih =>
    change count ≤ (edit (.raw count rest) parent children packet).length ∧
      Correct rest parent children ((packet.take count ++ edit rest parent children (packet.drop count)).drop count)
    refine ⟨by rw [edit_length]; exact recognized.1,?_⟩
    have length : (packet.take count).length = count := List.length_take_of_le recognized.1
    nth_rw 1 [← length]
    rw [List.drop_left]
    exact ih parent (packet.drop count) recognized.2
  | leaf rest ih =>
    cases packet with
    | nil => exact False.elim recognized
    | cons entry tail => cases entry with
      | none => exact False.elim recognized
      | some datum => cases datum with
        | header => exact False.elim recognized
        | real record => exact ⟨rfl,ih none tail recognized⟩
  | fork reverse =>
    cases packet with
    | nil => exact False.elim recognized
    | cons entry tail => cases entry with
      | none => exact False.elim recognized
      | some datum => cases datum with
        | header => exact False.elim recognized
        | real => rfl
  | «prefix» =>
    cases packet with
    | nil => exact False.elim recognized
    | cons entry tail => cases entry with
      | none => exact False.elim recognized
      | some datum => cases datum with
        | header => exact False.elim recognized
        | real => rfl

def TreeRecognizes : Source κ Layers → Source β (Cell α ρ ι) → Prop
  | .leaf _ plan,source => Recognizes plan source.rootRecord.2
  | .fork plan left right,.fork record l r => Recognizes plan record.2 ∧ TreeRecognizes left l ∧ TreeRecognizes right r
  | .fork _ _ _,.leaf _ _ => False

def TreeCorrect : Source κ Layers → Option ι → Source β (Cell α ρ ι) → Prop
  | .leaf _ plan,parent,source => Correct plan parent none source.rootRecord.2
  | .fork plan left right,parent,.fork record l r =>
      Correct plan parent (some (l.rootRecord.1,r.rootRecord.1)) record.2 ∧
      TreeCorrect left (childParent plan record.1) l ∧ TreeCorrect right (childParent plan record.1) r
  | .fork _ _ _,_,.leaf _ _ => False

theorem repacked_recognized (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    {plan : Source κ Layers} {context : Source κ (Expression α ρ ι)} (same : TreeMatches plan context)
    (source : Source β (Cell α ρ ι)) (repacked : Reached.Repacked blocks context source)
    (ordinary : Reached.Ordinary markerId blocks context) : TreeRecognizes plan source := by
  induction same generalizing source with
  | leaf key plan expression same =>
    cases repacked with
    | leaf _ _ block erases =>
      have recognized := recognizes_rebuilt block.rootRecord.1 (blocks key).rootRecord same
        (ordinary_ready markerId _ _ ordinary)
      cases block <;> exact recognized
  | fork plan expression left right a b same hl hr ihl ihr =>
    cases repacked with
    | fork _ _ _ l r id leftReady rightReady =>
      exact ⟨recognizes_rebuilt id [] same (ordinary_ready markerId [] _ ordinary.1),
        ihl l leftReady ordinary.2.1,ihr r rightReady ordinary.2.2⟩

theorem output_correct (context : Source κ Layers) (parent : Option ι) (source : Source β (Cell α ρ ι))
    (recognized : TreeRecognizes context source) : TreeCorrect context parent (output context parent source) := by
  induction context generalizing parent source with
  | leaf key plan =>
    have correct := edit_correct plan parent none source.rootRecord.2 recognized
    cases source <;> exact correct
  | fork plan left right ihl ihr => cases source with
    | leaf => exact False.elim recognized
    | fork record l r =>
      have leftId := congrArg Source.rootRecord (identifiers left (childParent plan record.1) l)
      have rightId := congrArg Source.rootRecord (identifiers right (childParent plan record.1) r)
      simp only [Source.mapRecords_root] at leftId rightId
      refine ⟨?_,ihl _ l recognized.2.1,ihr _ r recognized.2.2⟩
      change Correct plan parent
        (some ((output left (childParent plan record.1) l).rootRecord.1,
          (output right (childParent plan record.1) r).rootRecord.1))
        (edit plan parent (some (l.rootRecord.1,r.rootRecord.1)) record.2)
      rw [leftId,rightId]
      exact edit_correct plan parent _ record.2 recognized.1

end ChaCha.Paper20261030.MixedPacketRepair
