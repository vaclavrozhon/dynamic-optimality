import ChaCha.Paper20261030.CanonicalRoutingDecomposition

/-!
# Canonical real-wing views of a prepared head boundary

An active wing has two exposed logical forks and may contain the boundary
attachment. The two other pieces are the opaque prefix and tail. Their
actual packet ids, parent fields, and absence are recovered from the
tagged projection. A dormant wing has only the tail with a logical prefix.
-/

namespace ChaCha.Paper20261030.CanonicalHeadWingViews

open ColoredStorage SourcePointer Structural PhysicalPacketStaging CanonicalPacketLayerViews
open CanonicalRoutingDecomposition PacketLayers.Representation

variable {α β ρ ι : Type*}

/-- The opaque piece retains its actual tagged projection, including the
old external parent. This stronger witness is needed at the output. -/
def Canonical (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : ProjectionLocal.Projected α ρ) (piece : MixedHeadInputView.Physical β α ρ ι) : Prop :=
  ∃ (tagged : Option (Tagged α ρ ι)) (parent : Option ι),
    tagged.map (Source.mapRecords Prod.snd) = plain ∧ piece = render dummyId payload reverse parent tagged

def RootReady (piece : MixedHeadInputView.Physical β α ρ ι) : Prop :=
  ∀ source, piece = some source → PacketLayers.Ready source.rootRecord.2 (.prefix [])

theorem render_ready (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (tagged : Option (Tagged α ρ ι)) : RootReady (render dummyId payload reverse parent tagged) := by
  intro actual found
  cases tagged with
  | none => cases found
  | some source =>
    cases found
    simp only [Source.mapRecords_root]
    change PacketLayers.Ready (routing payload reverse parent source).rootRecord (.prefix [])
    cases source with
    | leaf key record =>
      rw [CanonicalPacketLayerViews.leaf]
      cases present : payload key <;> exact ⟨record.1,record.2,_,_,rfl⟩
    | fork record left right =>
      rw [CanonicalPacketLayerViews.fork]
      exact ⟨record.1,record.2,_,[],rfl⟩

def orientedJoin (reverse : Bool) (fields : MixedHeadInputView.JoinFields ι) (records : List ρ)
    (left right : MixedHeadInputView.Physical β α ρ ι) :=
  MixedHeadInputView.join fields records (if reverse then right else left) (if reverse then left else right)

theorem render_presence (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (tagged : Option (Tagged α ρ ι)) (plain : ProjectionLocal.Projected α ρ)
    (erases : tagged.map (Source.mapRecords Prod.snd) = plain) :
    (render dummyId payload reverse parent tagged).isSome = plain.isSome := by
  rw [← erases]
  simp only [render,Option.isSome_map]

theorem terminal (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (key : α) (record : ρ) (present : Bool) (tagged : Option (Tagged α ρ ι))
    (erases : tagged.map (Source.mapRecords Prod.snd) = if present then some (.leaf key [record]) else none) :
    ∃ packetId packetFields,
      render dummyId payload reverse parent tagged =
        if present then MixedHeadInputView.attach packetId packetFields record
          (some ((payload key).mapRecords (fun packet => (dummyId,packet)))) else none := by
  cases present with
  | false =>
    have absent : tagged = none := by simpa only [Bool.false_eq_true,if_false,Option.map_eq_none_iff] using erases
    subst tagged
    exact ⟨dummyId,placeholder,rfl⟩
  | true =>
    cases tagged with
    | none => cases erases
    | some tagged => cases tagged with
      | fork => cases erases
      | leaf actualKey actualRecord =>
        simp only [Option.map_some,Source.mapRecords,if_true,Option.some.injEq,Source.leaf.injEq] at erases
        obtain ⟨rfl,recordEq⟩ := erases
        rcases actualRecord with ⟨id,records⟩
        dsimp only at recordEq
        subst records
        refine ⟨id,fields Prod.fst (fun _ => (() : Unit)) parent (.leaf actualKey (id,[record])),?_⟩
        simp only [render,Option.map_some,CanonicalPacketLayerViews.leaf,if_true,
          MixedHeadInputView.attach,Source.mapRecords_setRoot,Source.mapRecords_root]

def activePacked (headPart tail : ProjectionLocal.Projected α ρ) (key : α) (boundaryPresent : Bool)
    (low high : List ρ) (terminal : ρ) : ProjectionLocal.Projected α ρ :=
  ProjectionLocal.decorate low (ProjectionLocal.join headPart
    (ProjectionLocal.decorate high (ProjectionLocal.join
      (if boundaryPresent then some (.leaf key [terminal]) else none) tail)))

def activeView (reverse boundaryPresent : Bool) (lower upper : MixedHeadInputView.JoinFields ι)
    (attachmentId : ι) (attachmentFields : Fields ι Unit)
    (low high : List ρ) (terminal : ρ)
    (headPart tail child : MixedHeadInputView.Physical β α ρ ι) : MixedHeadInputView.Physical β α ρ ι :=
  orientedJoin reverse lower low headPart
    (orientedJoin reverse upper high
      (if boundaryPresent then MixedHeadInputView.attach attachmentId attachmentFields terminal child else none) tail)

theorem active_canonical (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (headPart tail : ProjectionLocal.Projected α ρ) (key : α) (boundaryPresent : Bool)
    (low high : List ρ) (terminalRecord : ρ) (tagged : Option (Tagged α ρ ι))
    (erases : tagged.map (Source.mapRecords Prod.snd) = activePacked headPart tail key boundaryPresent low high terminalRecord) :
    ∃ physicalHead physicalTail lower upper attachmentId attachmentFields,
      physicalHead.isSome = headPart.isSome ∧ physicalTail.isSome = tail.isSome ∧
      render dummyId payload reverse parent tagged = activeView reverse boundaryPresent lower upper
        attachmentId attachmentFields low high terminalRecord physicalHead physicalTail
        (some ((payload key).mapRecords (fun packet => (dummyId,packet)))) ∧
      RootReady physicalHead ∧ RootReady physicalTail ∧
      Canonical dummyId payload reverse headPart physicalHead ∧ Canonical dummyId payload reverse tail physicalTail := by
  obtain ⟨taggedHead,taggedUpper,headParent,upperParent,lowerId,lowerFields,headErases,upperErases,lowerView⟩ :=
    join_decompose dummyId payload reverse parent low headPart
      (ProjectionLocal.decorate high (ProjectionLocal.join
        (if boundaryPresent then some (.leaf key [terminalRecord]) else none) tail)) tagged erases
  obtain ⟨taggedTerminal,taggedTail,terminalParent,tailParent,upperId,upperFields,terminalErases,tailErases,upperView⟩ :=
    join_decompose dummyId payload reverse upperParent high
      (if boundaryPresent then some (.leaf key [terminalRecord]) else none) tail taggedUpper upperErases
  obtain ⟨attachmentId,attachmentFields,terminalView⟩ :=
    terminal dummyId payload reverse terminalParent key terminalRecord boundaryPresent taggedTerminal terminalErases
  refine ⟨render dummyId payload reverse headParent taggedHead,render dummyId payload reverse tailParent taggedTail,
    ⟨dummyId,lowerId,lowerFields⟩,⟨dummyId,upperId,upperFields⟩,attachmentId,attachmentFields,
    render_presence dummyId payload reverse headParent taggedHead headPart headErases,
    render_presence dummyId payload reverse tailParent taggedTail tail tailErases,?_,
    render_ready dummyId payload reverse headParent taggedHead,render_ready dummyId payload reverse tailParent taggedTail,
    ⟨taggedHead,headParent,headErases,rfl⟩,⟨taggedTail,tailParent,tailErases,rfl⟩⟩
  rw [lowerView,upperView,terminalView]
  rfl

theorem active (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (headPart tail : ProjectionLocal.Projected α ρ) (key : α) (boundaryPresent : Bool)
    (low high : List ρ) (terminalRecord : ρ) (tagged : Option (Tagged α ρ ι))
    (erases : tagged.map (Source.mapRecords Prod.snd) = activePacked headPart tail key boundaryPresent low high terminalRecord) :
    ∃ physicalHead physicalTail lower upper attachmentId attachmentFields,
      physicalHead.isSome = headPart.isSome ∧ physicalTail.isSome = tail.isSome ∧
      render dummyId payload reverse parent tagged = activeView reverse boundaryPresent lower upper
        attachmentId attachmentFields low high terminalRecord physicalHead physicalTail
        (some ((payload key).mapRecords (fun packet => (dummyId,packet)))) ∧
      RootReady physicalHead ∧ RootReady physicalTail := by
  obtain ⟨ph,pt,lower,upper,id,fields,hp,tp,view,hr,tr,_,_⟩ :=
    active_canonical dummyId payload reverse parent headPart tail key boundaryPresent low high terminalRecord tagged erases
  exact ⟨ph,pt,lower,upper,id,fields,hp,tp,view,hr,tr⟩

theorem dormant_canonical (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (tail : ProjectionLocal.Projected α ρ) (high : List ρ) (tagged : Option (Tagged α ρ ι))
    (erases : tagged.map (Source.mapRecords Prod.snd) = ProjectionLocal.decorate high tail) :
    ∃ physicalTail : MixedHeadInputView.Physical β α ρ ι,
      physicalTail.isSome = tail.isSome ∧
      render dummyId payload reverse parent tagged = physicalTail.map (addRoot high) ∧ RootReady physicalTail ∧
      Canonical dummyId payload reverse tail physicalTail := by
  obtain ⟨taggedLeft,taggedTail,leftParent,tailParent,id,fields,leftErases,tailErases,view⟩ :=
    join_decompose dummyId payload reverse parent high none tail tagged erases
  have absent : taggedLeft = none := Option.map_eq_none_iff.mp leftErases
  subst taggedLeft
  refine ⟨render dummyId payload reverse tailParent taggedTail,
    render_presence dummyId payload reverse tailParent taggedTail tail tailErases,?_,render_ready dummyId payload reverse tailParent taggedTail,
    ⟨taggedTail,tailParent,tailErases,rfl⟩⟩
  rw [view]
  cases reverse <;> cases taggedTail <;> rfl

theorem dormant (dummyId : ι) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (parent : Option ι)
    (tail : ProjectionLocal.Projected α ρ) (high : List ρ) (tagged : Option (Tagged α ρ ι))
    (erases : tagged.map (Source.mapRecords Prod.snd) = ProjectionLocal.decorate high tail) :
    ∃ physicalTail : MixedHeadInputView.Physical β α ρ ι,
      physicalTail.isSome = tail.isSome ∧
      render dummyId payload reverse parent tagged = physicalTail.map (addRoot high) ∧ RootReady physicalTail := by
  obtain ⟨physical,present,view,ready,_⟩ := dormant_canonical dummyId payload reverse parent tail high tagged erases
  exact ⟨physical,present,view,ready⟩

end ChaCha.Paper20261030.CanonicalHeadWingViews
