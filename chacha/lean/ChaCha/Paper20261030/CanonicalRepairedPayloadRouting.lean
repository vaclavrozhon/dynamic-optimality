import ChaCha.Paper20261030.CanonicalRoutingPayloads
import ChaCha.Paper20261030.RepairedComponentLayout

set_option autoImplicit false

/-!
# Canonical repaired routing with independently reconstructed payloads

The payload predicate describes the component attached at each routing
leaf. This allows the new dormant component to be reconstructed inside
one active wing. Disjoint port sets combine independently reconstructed
payload witnesses; neither the program nor its control state receives
these witness trees or functions.
-/

namespace ChaCha.Paper20261030.CanonicalRepairedPayloadRouting

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair

variable {κ α β ρ ι : Type*}

def Represents (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool)
    (plain : Source α (List ρ)) (plan : Source κ Layers) (context : Source κ (Expression α ρ ι)) : Prop :=
  TreeMatches plan context ∧ HeadPacketLayout.Routing context.rootRecord ∧
  ∀ parent source, Reached.Repacked blocks context source →
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source →
    ∃ (tagged : Tagged α ρ ι) (payload : α → Source β (Packet α ρ ι)),
      tagged.mapRecords Prod.snd = plain ∧ (∀ key ∈ plain.shape.leaves, good key (payload key)) ∧
      (output plan parent source).mapRecords Prod.snd = routing payload reverse parent tagged ∧
      (output plan parent source).rootRecord.1 = tagged.rootRecord.1

theorem fixed (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : Source α (List ρ)) (plan : Source κ Layers) (context : Source κ (Expression α ρ ι))
    (represented : CanonicalRepairedRouting.Represents markerId blocks payload reverse plain plan context)
    (valid : ∀ key ∈ plain.shape.leaves, good key (payload key)) :
    Represents markerId blocks good reverse plain plan context := by
  refine ⟨represented.1,represented.2.1,?_⟩
  intro parent source repacked aligned
  obtain ⟨tagged,erases,view,id⟩ := represented.2.2 parent source repacked aligned
  exact ⟨tagged,payload,erases,valid,view,id⟩

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

theorem logical (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool)
    (plain : Source α (List ρ)) (plan : Source κ Layers) (context : Source κ (Expression α ρ ι))
    (represented : Represents markerId blocks good reverse plain plan context) (records : List ρ) :
    Represents markerId blocks good reverse (plain.setRoot (records++plain.rootRecord)) plan
      (context.setRoot (HeadPacketLayout.addLogical records context.rootRecord)) := by
  refine ⟨represented.1.logical records,?_,?_⟩
  · simp only [root_set]
    exact HeadPacketLayout.addLogical_routing records _ represented.2.1
  · intro parent target repacked aligned
    obtain ⟨source,sourcePacked,equality⟩ := Reached.logical_decomposition blocks context represented.2.1 records target repacked
    subst target
    obtain ⟨tagged,payload,erases,valid,view,id⟩ := represented.2.2 parent source sourcePacked
      ((prepend_alignment markerId records source).mp aligned)
    refine ⟨prepend records tagged,payload,?_,?_,?_,?_⟩
    · rw [prefix_erases,erases]
    · simpa only [source_setRoot_shape] using valid
    · rw [output_prepend plan (routing_of_matches represented.1.root represented.2.1),Source.mapRecords_setRoot,
        ← Source.mapRecords_root Prod.snd,view,logical_prefix]
    · rw [output_prepend plan (routing_of_matches represented.1.root represented.2.1)]
      simpa only [prepend,root_set] using id

theorem fork (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool) (records : List ρ)
    (leftPlain rightPlain : Source α (List ρ)) (leftPlan rightPlan : Source κ Layers)
    (leftContext rightContext : Source κ (Expression α ρ ι))
    (separate : ∀ key, key ∈ leftPlain.shape.leaves → key ∈ rightPlain.shape.leaves → False)
    (leftRep : Represents markerId blocks good reverse leftPlain leftPlan leftContext)
    (rightRep : Represents markerId blocks good reverse rightPlain rightPlan rightContext) :
    Represents markerId blocks good reverse
      (.fork records (if reverse then rightPlain else leftPlain) (if reverse then leftPlain else rightPlain))
      (.fork (.fork reverse) leftPlan rightPlan)
      (.fork (.whole markerId records placeholder .base) leftContext rightContext) := by
  classical
  refine ⟨.fork _ _ _ _ _ _ (.fork reverse markerId records placeholder) leftRep.1 rightRep.1,trivial,?_⟩
  intro parent source repacked aligned
  cases repacked with
  | fork _ _ _ l r id hl hr =>
    obtain ⟨_,leftAligned,rightAligned⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
    obtain ⟨leftTagged,leftPayload,leftErases,leftGood,leftView,leftId⟩ := leftRep.2.2 (some id) l hl leftAligned
    obtain ⟨rightTagged,rightPayload,rightErases,rightGood,rightView,rightId⟩ := rightRep.2.2 (some id) r hr rightAligned
    let payload := fun key => if key ∈ leftPlain.shape.leaves then leftPayload key else rightPayload key
    have leftShape : leftTagged.shape = leftPlain.shape := by rw [← leftErases,Source.mapRecords_shape]
    have rightShape : rightTagged.shape = rightPlain.shape := by rw [← rightErases,Source.mapRecords_shape]
    have leftEqual : ∀ key ∈ leftPlain.shape.leaves, leftPayload key = payload key := by
      intro key member
      simp only [payload,member,if_true]
    have rightEqual : ∀ key ∈ rightPlain.shape.leaves, rightPayload key = payload key := by
      intro key member
      simp only [payload,show key ∉ leftPlain.shape.leaves from fun both => separate key both member,if_false]
    have leftCanonical := leftView.trans (routing_payload_congr leftPayload payload reverse (some id) leftTagged
      (by simpa only [leftShape] using leftEqual))
    have rightCanonical := rightView.trans (routing_payload_congr rightPayload payload reverse (some id) rightTagged
      (by simpa only [rightShape] using rightEqual))
    have leftValid : ∀ key ∈ leftPlain.shape.leaves, good key (payload key) := by
      intro key member
      rw [← leftEqual key member]
      exact leftGood key member
    have rightValid : ∀ key ∈ rightPlain.shape.leaves, good key (payload key) := by
      intro key member
      rw [← rightEqual key member]
      exact rightGood key member
    have leftRoot := congrArg Source.rootRecord (identifiers leftPlan (some id) l)
    have rightRoot := congrArg Source.rootRecord (identifiers rightPlan (some id) r)
    simp only [Source.mapRecords_root] at leftRoot rightRoot
    refine ⟨.fork (id,records) (if reverse then rightTagged else leftTagged) (if reverse then leftTagged else rightTagged),payload,?_,?_,?_,rfl⟩
    · cases reverse <;> simp only [Source.mapRecords,Bool.false_eq_true,if_false,if_true,leftErases,rightErases]
    · cases reverse <;> intro key member <;> rcases List.mem_append.mp member with member | member
      · exact leftValid key member
      · exact rightValid key member
      · exact rightValid key member
      · exact leftValid key member
    · exact CanonicalMixedPacketRepair.routing_fork payload reverse parent id records placeholder leftPlan rightPlan l r
        leftTagged rightTagged (leftRoot.symm.trans leftId) (rightRoot.symm.trans rightId) leftCanonical rightCanonical

theorem attachment (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool) (key : α) (record : ρ)
    (plan : Source κ Layers) (context : Source κ (Expression α ρ ι))
    (childRep : RepairedComponentLayout.Represents markerId blocks (some plan) (some context)
      (fun view => ∃ body, good key body ∧ view = some body)) :
    Represents markerId blocks good reverse (.leaf key [record])
      (plan.setRoot (.leaf (.raw 1 plan.rootRecord)))
      (context.setRoot (.whole markerId [record] placeholder (.raw [none] context.rootRecord))) := by
  refine ⟨childRep.1.setRoot _ _ (.leaf markerId [record] placeholder _ _ (.raw [none] _ _ childRep.1.root)),?_,?_⟩
  · simp only [root_set,HeadPacketLayout.Routing]
  · intro parent target repacked aligned
    obtain ⟨source,sourcePacked,equality⟩ := Reached.attachment_decomposition blocks context markerId [record] placeholder target repacked
    subst target
    have sourceAligned := raw_alignment_tail markerId [some (.real ((source.rootRecord.1,[record]),placeholder)),none] source aligned
    obtain ⟨body,bodyGood,bodyView⟩ := childRep.2 source sourcePacked sourceAligned
    have bodyEqual := Option.some.inj bodyView
    let tagged : Tagged α ρ ι := .leaf key ((output plan none source).rootRecord.1,[record])
    refine ⟨tagged,(fun _ => body),rfl,?_,?_,?_⟩
    · intro other member
      have same : other = key := by simpa only [Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
      subst other
      exact bodyGood
    · rw [CanonicalMixedPacketRepair.attachment plan parent [record] placeholder source (childRep.1.repacked_fits blocks source sourcePacked),
        Source.mapRecords_setRoot,CanonicalPacketLayerViews.leaf,← bodyEqual,Source.mapRecords_root]
      rfl
    · rw [CanonicalMixedPacketRepair.attachment plan parent [record] placeholder source (childRep.1.repacked_fits blocks source sourcePacked)]
      rw [root_set]
      rfl

end ChaCha.Paper20261030.CanonicalRepairedPayloadRouting
