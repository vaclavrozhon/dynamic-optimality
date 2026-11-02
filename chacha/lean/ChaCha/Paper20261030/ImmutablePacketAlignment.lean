import ChaCha.Paper20261030.ImmutableSourceRecordInvariant
import ChaCha.Paper20261030.LocalPhysicalPacketStaging
import ChaCha.Paper20261030.LocalRecordActions

/-!
# Physical packet ids remain attached to their actual vertices

The reserved marker id distinguishes temporary logical-prefix markers
from ordinary physical packets. Every ordinary packet at a reached
vertex must agree with that vertex's immutable id. Header datums and
delimiters carry no physical-vertex id in this invariant.

Deleting prefixes preserves the invariant. Inserting markers, headers,
or delimiters preserves it for every reached id. The actual immutable-id
compiler therefore maintains alignment through record edits, navigation,
and rotations, including records inside opaque blocks and the outer tree.
-/

namespace ChaCha.Paper20261030.PacketAlignment

open ColoredStorage SourcePointer SourceLocalProgram PhysicalPacketStaging

variable {α β ρ ι : Type*}

def Entry (markerId vertexId : ι) : Option (Datum α ρ ι) → Prop
  | some (.real ((storedId,_),_)) => storedId = markerId ∨ storedId = vertexId
  | _ => True

def Aligned (markerId vertexId : ι) (packet : Packet α ρ ι) : Prop :=
  ∀ entry ∈ packet, Entry markerId vertexId entry

def Neutral (markerId : ι) (packet : Packet α ρ ι) : Prop := ∀ vertexId, Aligned markerId vertexId packet

def Predicate (markerId : ι) (record : ι × Packet α ρ ι) : Prop := Aligned markerId record.1 record.2

theorem append (markerId vertexId : ι) (before after : Packet α ρ ι)
    (hb : Aligned markerId vertexId before) (ha : Aligned markerId vertexId after) :
    Aligned markerId vertexId (before++after) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact hb entry member
  · exact ha entry member

theorem drop (markerId vertexId : ι) (packet : Packet α ρ ι) (count : Nat)
    (valid : Aligned markerId vertexId packet) : Aligned markerId vertexId (packet.drop count) :=
  fun entry member => valid entry (List.mem_of_mem_drop member)

theorem markers (markerId : ι) (records : List ρ) : Neutral markerId (records.map (marker (α := α) markerId)) := by
  intro vertexId entry member
  obtain ⟨record,_,rfl⟩ := List.mem_map.mp member
  exact Or.inl rfl

theorem header (markerId : ι) (stored : VirtualHeaderController.Virtual α (PhysicalForestMetadata.Record ρ ι)) :
    Neutral markerId [some (.header stored),none] := by
  intro vertexId entry member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> trivial

theorem stored_id (markerId vertexId storedId : ι) (records : List ρ) (fields : Structural.Fields ι Unit)
    (before rest : Packet α ρ ι) (valid : Aligned markerId vertexId (before++some (.real ((storedId,records),fields))::rest))
    (ordinary : storedId ≠ markerId) : storedId = vertexId := by
  have atPacket := valid _ (List.mem_append_right before (List.mem_cons_self))
  exact atPacket.resolve_left ordinary

def SafeAction (markerId : ι) : LocalRecordActions.Action (Option (Datum α ρ ι)) → Prop
  | .prepend records => Neutral markerId records
  | _ => True

def SafeActions (markerId : ι) (actions : List (LocalRecordActions.Action (Option (Datum α ρ ι)))) : Prop :=
  ∀ action ∈ actions, SafeAction markerId action

theorem safe_tail (markerId : ι) (action : LocalRecordActions.Action (Option (Datum α ρ ι)))
    (rest : List (LocalRecordActions.Action (Option (Datum α ρ ι))))
    (valid : SafeActions markerId (action::rest)) : SafeActions markerId rest :=
  fun next member => valid next (List.mem_cons_of_mem _ member)

def StateValid (markerId : ι) : LocalRecordActions.State (Option (Datum α ρ ι)) → ι → Prop
  | .ready actions,_ => SafeActions markerId actions
  | .writing records rest,vertexId => Aligned markerId vertexId records ∧ SafeActions markerId rest

theorem rules (markerId : ι) :
    ImmutableSourceRecordInvariant.Rules LocalRecordActions.program (Predicate (α := α) (ρ := ρ) markerId) (StateValid markerId) := by
  constructor
  · intro state next instruction vertexId packet leaf stateValid packetValid
    cases state with
    | writing => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
    | ready actions => cases actions with
      | nil => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
      | cons action rest =>
        have tail := safe_tail markerId action rest stateValid
        cases action with
        | nav => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
        | pop =>
          simp only [LocalRecordActions.program,Instruction.read.injEq] at instruction
          cases instruction
          exact ⟨by simpa only [List.drop_one] using drop markerId vertexId packet 1 packetValid,tail⟩
        | drop count =>
          simp only [LocalRecordActions.program,Instruction.read.injEq] at instruction
          cases instruction
          exact ⟨drop markerId vertexId packet count packetValid,tail⟩
        | prepend records =>
          have neutral := stateValid _ (List.mem_cons_self)
          simp only [LocalRecordActions.program,Instruction.read.injEq] at instruction
          cases instruction
          exact ⟨append markerId vertexId records packet (neutral vertexId) packetValid,tail⟩
  · intro state action next instruction oldId newId valid
    cases state with
    | writing => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
    | ready actions => cases actions with
      | nil => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
      | cons first rest => cases first with
        | pop | drop | prepend => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
        | nav move =>
          simp only [LocalRecordActions.program,Instruction.nav.injEq] at instruction
          rcases instruction with ⟨rfl,rfl⟩
          exact safe_tail markerId (.nav move) rest valid
  · intro state fresh next instruction vertexId valid
    cases state with
    | writing records rest =>
      simp only [LocalRecordActions.program,Instruction.write.injEq] at instruction
      rcases instruction with ⟨rfl,rfl⟩
      exact valid
    | ready actions => cases actions with
      | nil => simp only [LocalRecordActions.program,reduceCtorEq] at instruction
      | cons action rest => cases action <;> simp only [LocalRecordActions.program,reduceCtorEq] at instruction

theorem run {actions : List (LocalRecordActions.Action (Option (Datum α ρ ι)))}
    (markerId : ι) (safe : SafeActions markerId actions)
    {before after : Cursor β (ι × Packet α ρ ι)} {reads cost}
    (actual : Run (ImmutableSource.program LocalRecordActions.program) (.ready (.ready actions)) before
      (.ready (.ready [])) after reads cost)
    (aligned : SourceRecordPredicate.Holds (Predicate markerId) before.tree) :
    SourceRecordPredicate.Holds (Predicate markerId) after.tree :=
  (ImmutableSourceRecordInvariant.run _ _ _ (rules markerId) actual safe aligned).2

end ChaCha.Paper20261030.PacketAlignment
