import TangoSquared.Paper20261030.LocalReachedPacketStaging

/-!
# Compositional input representation for mixed packet layouts

These lemmas derive the staging precondition from actual physical joins,
prefix merging, attachment packets, and raw headers. Old physical ids and
fields are ghost parameters of the representation proof, never controller
inputs. Applying the lemmas to a prepared canonical component additionally
requires decomposing its packed color projections at the exposed forks.
-/

namespace TangoSquared.Paper20261030.PacketLayers.Representation

open ColoredStorage SourcePointer Structural PhysicalPacketStaging

variable {κ α β ρ ι : Type*}

def base (blocks : κ → Source β (Packet α ρ ι)) : Source κ (Expression α ρ ι) → Packet α ρ ι
  | .leaf key _ => (blocks key).rootRecord
  | .fork _ _ _ => []

theorem prepend_nil (packet : Packet α ρ ι) : PhysicalPacketStaging.Context.prependLogical [] packet = packet := by
  cases packet with
  | nil => rfl
  | cons entry rest => cases entry with
    | none => rfl
    | some datum => cases datum <;> rfl

theorem prepend_append (first last : List ρ) (packet : Packet α ρ ι) :
    PhysicalPacketStaging.Context.prependLogical first (PhysicalPacketStaging.Context.prependLogical last packet) =
      PhysicalPacketStaging.Context.prependLogical (first++last) packet := by
  cases packet with
  | nil => rfl
  | cons entry rest => cases entry with
    | none => rfl
    | some datum => cases datum with
      | header => rfl
      | real record =>
        rcases record with ⟨⟨id,records⟩,fields⟩
        simp only [PhysicalPacketStaging.Context.prependLogical,List.append_assoc]

theorem matches_prepend (records : List ρ) (base : Packet α ρ ι) (expression : Expression α ρ ι)
    (packet : Packet α ρ ι) (routing : HeadPacketLayout.Routing expression)
    (matching : Matches base expression packet) :
    Matches base (HeadPacketLayout.addLogical records expression)
      (PhysicalPacketStaging.Context.prependLogical records packet) := by
  cases expression with
  | base | raw => exact False.elim routing
  | whole id tail fields rest =>
    obtain ⟨actualId,actualFields,suffix,rfl,tailMatch⟩ := matching
    exact ⟨actualId,actualFields,suffix,rfl,tailMatch⟩
  | «prefix» tail =>
    change PhysicalPacketStaging.Context.prependLogical records packet = _
    rw [matching,prepend_append]

theorem root_matches (blocks : κ → Source β (Packet α ρ ι)) (context : Source κ (Expression α ρ ι))
    (source : Source β (Context.Cell α ρ ι)) (stored : Reached.Stored blocks context source) :
    Matches (base blocks context) context.rootRecord source.rootRecord.2 := by
  cases context with
  | leaf => exact stored.2
  | fork => cases source with
    | leaf => exact False.elim stored
    | fork => exact stored.1

theorem setRoot (blocks : κ → Source β (Packet α ρ ι)) (context : Source κ (Expression α ρ ι))
    (source : Source β (Context.Cell α ρ ι)) (stored : Reached.Stored blocks context source)
    (expression : Expression α ρ ι) (packet : Packet α ρ ι)
    (matching : Matches (base blocks context) expression packet) :
    Reached.Stored blocks (context.setRoot expression) (source.setRoot (source.rootRecord.1,packet)) := by
  cases context with
  | leaf key old =>
    refine ⟨?_,?_⟩
    · cases source <;> exact stored.1
    · cases source <;> exact matching
  | fork old left right => cases source with
    | leaf => exact False.elim stored
    | fork => exact ⟨matching,stored.2⟩

def addRoot (records : List ρ) (source : Source β (Context.Cell α ρ ι)) : Source β (Context.Cell α ρ ι) :=
  source.setRoot (source.rootRecord.1,PhysicalPacketStaging.Context.prependLogical records source.rootRecord.2)

theorem logical (blocks : κ → Source β (Packet α ρ ι)) (context : Source κ (Expression α ρ ι))
    (source : Source β (Context.Cell α ρ ι)) (stored : Reached.Stored blocks context source)
    (records : List ρ) (routing : HeadPacketLayout.Routing context.rootRecord) :
    Reached.Stored blocks (context.setRoot (HeadPacketLayout.addLogical records context.rootRecord)) (addRoot records source) :=
  setRoot blocks context source stored _ _ (matches_prepend records _ _ _ routing (root_matches blocks context source stored))

def Holds (blocks : κ → Source β (Packet α ρ ι)) :
    HeadPacketLayout.Layout κ α ρ ι → Option (Source β (Context.Cell α ρ ι)) → Prop
  | none,none => True
  | some context,some source => Reached.Stored blocks context source
  | _,_ => False

def physicalJoin (vertexId packetId : ι) (fields : Fields ι Unit) (records : List ρ) :
    Option (Source β (Context.Cell α ρ ι)) → Option (Source β (Context.Cell α ρ ι)) → Option (Source β (Context.Cell α ρ ι))
  | none,none => none
  | some left,none => some (addRoot records left)
  | none,some right => some (addRoot records right)
  | some left,some right => some (.fork (vertexId,[some (.real ((packetId,records),fields))]) left right)

theorem realJoin (markerId vertexId packetId : ι) (fields : Fields ι Unit) (records : List ρ)
    (blocks : κ → Source β (Packet α ρ ι)) (left right : HeadPacketLayout.Layout κ α ρ ι)
    (leftTree rightTree : Option (Source β (Context.Cell α ρ ι)))
    (leftStored : Holds blocks left leftTree) (rightStored : Holds blocks right rightTree)
    (leftRouting : HeadPacketLayout.RoutingRoot left) (rightRouting : HeadPacketLayout.RoutingRoot right) :
    Holds blocks (HeadPacketLayout.realJoin markerId records left right)
      (physicalJoin vertexId packetId fields records leftTree rightTree) := by
  cases left <;> cases leftTree <;> try exact False.elim leftStored
  all_goals cases right <;> cases rightTree <;> try exact False.elim rightStored
  · trivial
  · exact logical blocks _ _ rightStored records rightRouting
  · exact logical blocks _ _ leftStored records leftRouting
  · exact ⟨⟨packetId,fields,[],rfl,rfl⟩,leftStored,rightStored⟩

def physicalPrimaryJoin (vertexId : ι) :
    Option (Source β (Context.Cell α ρ ι)) → Option (Source β (Context.Cell α ρ ι)) → Option (Source β (Context.Cell α ρ ι))
  | none,right => right
  | left,none => left
  | some left,some right => some (.fork (vertexId,[]) left right)

theorem primaryJoin (vertexId : ι) (blocks : κ → Source β (Packet α ρ ι)) (left right : HeadPacketLayout.Layout κ α ρ ι)
    (leftTree rightTree : Option (Source β (Context.Cell α ρ ι)))
    (leftStored : Holds blocks left leftTree) (rightStored : Holds blocks right rightTree) :
    Holds blocks (HeadPacketLayout.primaryJoin left right) (physicalPrimaryJoin vertexId leftTree rightTree) := by
  cases left <;> cases leftTree <;> try exact False.elim leftStored
  all_goals cases right <;> cases rightTree <;> try exact False.elim rightStored
  · trivial
  · exact rightStored
  · exact leftStored
  · exact ⟨rfl,leftStored,rightStored⟩

theorem attachment (markerId packetId : ι) (fields : Fields ι Unit) (record : ρ)
    (blocks : κ → Source β (Packet α ρ ι)) (context : Source κ (Expression α ρ ι))
    (source : Source β (Context.Cell α ρ ι)) (stored : Reached.Stored blocks context source) :
    Reached.Stored blocks
      (context.setRoot (.whole markerId [record] placeholder (.raw [none] context.rootRecord)))
      (source.setRoot (source.rootRecord.1,some (.real ((packetId,[record]),fields)) :: none :: source.rootRecord.2)) :=
  setRoot blocks context source stored _ _ ⟨packetId,fields,none :: source.rootRecord.2,rfl,
    ⟨source.rootRecord.2,rfl,root_matches blocks context source stored⟩⟩

theorem block (blocks : κ → Source β (Packet α ρ ι)) (key : κ) (source : Source β (Context.Cell α ρ ι))
    (erases : source.mapRecords Prod.snd = blocks key) : Reached.Stored blocks (.leaf key (.prefix [])) source := by
  refine ⟨?_,?_⟩
  · rw [erases]
    cases blocks key <;> rfl
  · change source.rootRecord.2 = PhysicalPacketStaging.Context.prependLogical [] (blocks key).rootRecord
    rw [prepend_nil,← erases,Source.mapRecords_root]

theorem bottom (blocks : κ → Source β (Packet α ρ ι)) (key : κ) (label : β) (id : ι) (header : Packet α ρ ι)
    (bare : blocks key = .leaf label []) :
    Reached.Stored blocks (.leaf key (.raw header .base)) (.leaf label (id,header)) := by
  refine ⟨?_,⟨[],by simp only [List.append_nil,Source.rootRecord],?_⟩⟩
  · simp only [bare,Source.mapRecords,Source.rootRecord,Source.setRoot]
  · simp only [Matches,bare,Source.rootRecord]

end TangoSquared.Paper20261030.PacketLayers.Representation
