import ChaCha.Paper20261030.CanonicalPreparedComponentViews
import ChaCha.Paper20261030.RootMixedHeadExchange

/-! Canonical active input at a zero-depth boundary. The source has only
one exposed fork. Reusing the finite wing view with an absent prefix and
an empty low list adds no source vertex or physical packet. -/

namespace ChaCha.Paper20261030.CanonicalRootComponentView

open ColoredStorage SourcePointer Structural HeadBoundary PhysicalForestMetadata PhysicalPacketStaging
open PacketLayers.Representation CanonicalRoutingDecomposition CanonicalComponentAssembly
open CanonicalPreparedComponentViews LocalComponentCompiler
open ObservedHeadBlueprint (owned)

variable {α β ρ ι η : Type*} [DecidableEq α]

local instance : LinearOrder (Option Bool) := inferInstanceAs (LinearOrder (WithBot Bool))

def observed (identifier : ρ → η) (activeColor incomingColor : α → Option Bool)
    (oldHigh incomingHigh oldTerminal incomingTerminal : ρ) (depth : α) (oldTail incomingTail : Source α ρ) : RootRecords ρ η :=
  ⟨(oldHigh,fields identifier activeColor none (.fork oldHigh (.leaf depth oldTerminal) oldTail)),
    (incomingHigh,fields identifier incomingColor none (.fork incomingHigh (.leaf depth incomingTerminal) incomingTail)),
    (oldTerminal,fields identifier activeColor (some (identifier oldHigh)) (.leaf depth oldTerminal)),
    (incomingTerminal,fields identifier incomingColor (some (identifier incomingHigh)) (.leaf depth incomingTerminal))⟩

theorem packing (identifier : ρ → η) (color : α → Option Bool) (side direction : Bool)
    (high terminal : ρ) (depth : α) (tail : Source α ρ) (boundary : color depth = some direction) :
    packed color (some side) (annotate identifier color none (.fork high (.leaf depth terminal) tail)) =
      CanonicalHeadWingViews.activePacked none
        (packed color (some side) (annotate identifier color (some (identifier high)) tail)) depth (decide (side = direction)) []
        (owned (some side) (high,fields identifier color none (.fork high (.leaf depth terminal) tail)))
        (terminal,fields identifier color (some (identifier high)) (.leaf depth terminal)) := by
  have leaf : packed color (some side) (annotate identifier color (some (identifier high)) (.leaf depth terminal)) =
      if decide (side = direction) then
        some (.leaf depth [(terminal,fields identifier color (some (identifier high)) (.leaf depth terminal))]) else none := by
    cases side <;> cases direction <;>
      simp only [annotate,packed,pack,boundary,Option.some.injEq,reduceCtorEq,if_true,if_false,decide_true,decide_false,
        Bool.false_eq_true,Stored.toSource]
  rw [AnnotatedHeadWingPacking.fork,leaf]
  simp only [CanonicalHeadWingViews.activePacked,ProjectionLocal.join,ProjectionLocal.decorate_nil]

private theorem join_none_left (fields : MixedHeadInputView.JoinFields ι) (records : List (Logical ρ η))
    (right : MixedHeadInputView.Physical β α (Logical ρ η) ι) :
    MixedHeadInputView.join fields records none right = right.map (addRoot records) := by cases right <;> rfl

private theorem join_none_right (fields : MixedHeadInputView.JoinFields ι) (records : List (Logical ρ η))
    (left : MixedHeadInputView.Physical β α (Logical ρ η) ι) :
    MixedHeadInputView.join fields records left none = left.map (addRoot records) := by cases left <;> rfl

theorem active (dummyId : ι) (identifier : ρ → η) (color : α → Option Bool)
    (high terminal : ρ) (depth : α) (tail : Source α ρ) (direction : Bool) (boundary : color depth = some direction)
    (forest : TaggedForest (Option Bool) α (Logical ρ η) ι)
    (represented : ProjectionForest.Represents color
      ⟨annotate identifier color none (.fork high (.leaf depth terminal) tail),[]⟩ (erase forest))
    (headerKey : α) (payload : Option Bool → α → Source β (Packet α (Logical ρ η) ι))
    (config : MultiSourceProgram.Configuration (Option Bool) β (Packet α (Logical ρ η) ι))
    (assembled : ForestConnector.assemble
      (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))
      (ForestConnector.ThreeColors.layout (ComponentPhysicalRepair.view none wingOrientation headerKey payload (encode forest))) = some config) :
    ∃ (tailLeft tailRight : MixedHeadInputView.Physical β α (Logical ρ η) ι) (actualFields : MixedHeadInputView.ActiveFields ι),
      tailLeft.isSome = (packed color (some true) (annotate identifier color (some (identifier high)) tail)).isSome ∧
      tailRight.isSome = (packed color (some false) (annotate identifier color (some (identifier high)) tail)).isSome ∧
      some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
        activeView actualFields direction (terminal,⟨none,∅,none⟩)
          (high,fields identifier color none (.fork high (.leaf depth terminal) tail))
          (terminal,fields identifier color (some (identifier high)) (.leaf depth terminal))
          (header forest) none none tailLeft tailRight
          (some ((payload (some direction) depth).mapRecords (fun packet => (dummyId,packet))))
          ((payload none headerKey).mapRecords (fun packet => (dummyId,packet))) ∧
      CanonicalHeadWingViews.RootReady tailLeft ∧ CanonicalHeadWingViews.RootReady tailRight ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some true)) false
        (packed color (some true) (annotate identifier color (some (identifier high)) tail)) tailLeft ∧
      CanonicalHeadWingViews.Canonical dummyId (payload (some false)) true
        (packed color (some false) (annotate identifier color (some (identifier high)) tail)) tailRight := by
  let source := annotate identifier color none (.fork high (.leaf depth terminal) tail)
  have erases (side : Bool) := packed_focus color source forest represented (some side)
  have leftPacking := (erases true).trans (packing identifier color true direction high terminal depth tail boundary)
  have rightPacking := (erases false).trans (packing identifier color false direction high terminal depth tail boundary)
  obtain ⟨headLeft,tailLeft,lowerLeft,upperLeft,leftId,leftFields,headLeftPresent,tailLeftPresent,leftView,_,tailLeftReady,_,tailLeftCanonical⟩ :=
    CanonicalHeadWingViews.active_canonical dummyId (payload (some true)) false none _ _ _ _ _ _ _ _ leftPacking
  obtain ⟨headRight,tailRight,lowerRight,upperRight,rightId,rightFields,headRightPresent,tailRightPresent,rightView,_,tailRightReady,_,tailRightCanonical⟩ :=
    CanonicalHeadWingViews.active_canonical dummyId (payload (some false)) true none _ _ _ _ _ _ _ _ rightPacking
  have headLeftNone : headLeft = none := by cases headLeft <;> first | rfl | cases headLeftPresent
  have headRightNone : headRight = none := by cases headRight <;> first | rfl | cases headRightPresent
  subst headLeft headRight
  let actualFields : MixedHeadInputView.ActiveFields ι := ⟨lowerLeft,lowerRight,upperLeft,upperRight,
    if direction then leftId else rightId,if direction then leftFields else rightFields,⟨dummyId,dummyId⟩⟩
  have virtual := CanonicalPacketLayerViews.component_virtual none wingOrientation headerKey payload forest
  have assembly := CanonicalComponentAssembly.assembled dummyId _ _ virtual config assembled
  rw [real_piece dummyId color source forest represented none (some true) (by simp) wingOrientation headerKey payload,
    real_piece dummyId color source forest represented none (some false) (by simp) wingOrientation headerKey payload,
    virtual_piece dummyId none wingOrientation headerKey payload forest] at assembly
  change some (config.tree.mapRecords (fun packet => (dummyId,packet))) =
    physicalPrimaryJoin dummyId
      (physicalPrimaryJoin dummyId (render dummyId (payload (some true)) false none ((forest (some true)).map Cursor.focus))
        (some (MixedHeadInputView.rawBlock (header forest) ((payload none headerKey).mapRecords (fun packet => (dummyId,packet))))))
      (render dummyId (payload (some false)) true none ((forest (some false)).map Cursor.focus)) at assembly
  rw [leftView,rightView] at assembly
  have lowEmpty (side : Bool) : owned (some side) ((terminal,⟨none,∅,none⟩) : Logical ρ η) = [] := rfl
  refine ⟨tailLeft,tailRight,actualFields,tailLeftPresent,tailRightPresent,?_,tailLeftReady,tailRightReady,tailLeftCanonical,tailRightCanonical⟩
  cases direction <;>
    simp only [activeView,actualFields,CanonicalHeadWingViews.activeView,CanonicalHeadWingViews.orientedJoin,lowEmpty,
      Bool.false_eq_true,reduceCtorEq,decide_false,decide_true,if_false,if_true,join_none_left,join_none_right] at assembly ⊢ <;>
    exact assembly

end ChaCha.Paper20261030.CanonicalRootComponentView
