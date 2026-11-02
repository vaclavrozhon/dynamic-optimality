import ChaCha.Paper20261030.RepackedRootTransform

set_option autoImplicit false

/-!
# Reconstructing a canonical routing projection after mixed repair

`Represents` states that every aligned repacked realization of a finite
layout repairs to a canonical routing tree. The tagged tree is recovered
from actual reached connector identifiers; its logical erasure is fixed
in advance. The representation is closed under collapsed logical prefixes
and genuine routing forks, including mirrored right wings.
-/

namespace ChaCha.Paper20261030.CanonicalRepairedRouting

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair

variable {κ α β ρ ι : Type*}

def Represents (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : Source α (List ρ)) (plan : Source κ Layers) (context : Source κ (Expression α ρ ι)) : Prop :=
  TreeMatches plan context ∧ HeadPacketLayout.Routing context.rootRecord ∧
  ∀ parent source, Reached.Repacked blocks context source →
    SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source →
    ∃ tagged : Tagged α ρ ι, tagged.mapRecords Prod.snd = plain ∧
      (output plan parent source).mapRecords Prod.snd = routing payload reverse parent tagged ∧
      (output plan parent source).rootRecord.1 = tagged.rootRecord.1

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

theorem opaque_block (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (key : κ)
    (oldParent : Option ι) (tagged : Tagged α ρ ι) (records : List ρ)
    (blockView : blocks key = routing payload reverse oldParent tagged)
    (ordinary : tagged.rootRecord.1 ≠ markerId) :
    Represents markerId blocks payload reverse
      ((tagged.mapRecords Prod.snd).setRoot (records++(tagged.mapRecords Prod.snd).rootRecord))
      (.leaf key .prefix) (.leaf key (.prefix records)) := by
  refine ⟨.leaf key _ _ (.prefix records),trivial,?_⟩
  intro parent source repacked aligned
  cases repacked with
  | leaf _ _ block erases =>
    have blockEq := erases.trans blockView
    have before : (block.setRoot (block.rootRecord.1,rebuilt block.rootRecord.1 (blocks key).rootRecord (.prefix records))).mapRecords Prod.snd =
        routing payload reverse oldParent (prepend records tagged) := by
      simp only [Source.mapRecords_setRoot,rebuilt,erases,blockView,logical_prefix]
    have atRoot := SourceRecordPredicate.root _ _ aligned
    have id := CanonicalMixedPacketRepair.routing_root_id_of_ordinary markerId payload reverse oldParent
      (prepend records tagged) _ before atRoot (by simpa only [prepend,root_set] using ordinary)
    refine ⟨prepend records tagged,prefix_erases records tagged,?_,?_⟩
    · rw [blockView]
      exact CanonicalMixedPacketRepair.opaque_block key records parent oldParent payload reverse tagged block blockEq
    · simpa only [output,cell,root_set] using id

theorem logical (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : Source α (List ρ)) (plan : Source κ Layers) (context : Source κ (Expression α ρ ι))
    (represented : Represents markerId blocks payload reverse plain plan context) (records : List ρ) :
    Represents markerId blocks payload reverse (plain.setRoot (records++plain.rootRecord)) plan
      (context.setRoot (HeadPacketLayout.addLogical records context.rootRecord)) := by
  refine ⟨represented.1.logical records,?_,?_⟩
  · simp only [root_set]
    exact HeadPacketLayout.addLogical_routing records _ represented.2.1
  · intro parent target repacked aligned
    obtain ⟨source,sourcePacked,equality⟩ := Reached.logical_decomposition blocks context represented.2.1 records target repacked
    subst target
    have sourceAligned := (prepend_alignment markerId records source).mp aligned
    obtain ⟨tagged,erases,view,id⟩ := represented.2.2 parent source sourcePacked sourceAligned
    refine ⟨prepend records tagged,?_,?_,?_⟩
    · rw [prefix_erases,erases]
    · rw [output_prepend plan (routing_of_matches represented.1.root represented.2.1),Source.mapRecords_setRoot,
        ← Source.mapRecords_root Prod.snd,view,logical_prefix]
    · rw [output_prepend plan (routing_of_matches represented.1.root represented.2.1)]
      simpa only [prepend,root_set] using id

theorem fork (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (records : List ρ)
    (leftPlain rightPlain : Source α (List ρ)) (leftPlan rightPlan : Source κ Layers)
    (leftContext rightContext : Source κ (Expression α ρ ι))
    (leftRep : Represents markerId blocks payload reverse leftPlain leftPlan leftContext)
    (rightRep : Represents markerId blocks payload reverse rightPlain rightPlan rightContext) :
    Represents markerId blocks payload reverse
      (.fork records (if reverse then rightPlain else leftPlain) (if reverse then leftPlain else rightPlain))
      (.fork (.fork reverse) leftPlan rightPlan)
      (.fork (.whole markerId records placeholder .base) leftContext rightContext) := by
  refine ⟨.fork _ _ _ _ _ _ (.fork reverse markerId records placeholder) leftRep.1 rightRep.1,trivial,?_⟩
  intro parent source repacked aligned
  cases repacked with
  | fork _ _ _ l r id hl hr =>
    obtain ⟨_,leftAligned,rightAligned⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
    obtain ⟨leftTagged,leftErases,leftView,leftId⟩ := leftRep.2.2 (some id) l hl leftAligned
    obtain ⟨rightTagged,rightErases,rightView,rightId⟩ := rightRep.2.2 (some id) r hr rightAligned
    have leftRoot := congrArg Source.rootRecord (identifiers leftPlan (some id) l)
    have rightRoot := congrArg Source.rootRecord (identifiers rightPlan (some id) r)
    simp only [Source.mapRecords_root] at leftRoot rightRoot
    refine ⟨.fork (id,records) (if reverse then rightTagged else leftTagged) (if reverse then leftTagged else rightTagged),?_,?_,rfl⟩
    · cases reverse <;> simp only [Source.mapRecords,Bool.false_eq_true,if_false,if_true,leftErases,rightErases]
    · exact CanonicalMixedPacketRepair.routing_fork payload reverse parent id records placeholder leftPlan rightPlan l r
        leftTagged rightTagged (leftRoot.symm.trans leftId) (rightRoot.symm.trans rightId) leftView rightView

/-- Optional layouts describe absent color projections without allocating
a dummy physical vertex. -/
def Layout (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) :
    ProjectionLocal.Projected α ρ → HeadPacketRepair.Layout κ → HeadPacketLayout.Layout κ α ρ ι → Prop
  | none,none,none => True
  | some plain,some plan,some context => Represents markerId blocks payload reverse plain plan context
  | _,_,_ => False

theorem logical_layout (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : ProjectionLocal.Projected α ρ) (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (represented : Layout markerId blocks payload reverse plain plan context) (records : List ρ) :
    Layout markerId blocks payload reverse (ProjectionLocal.decorate records plain) plan
      (HeadPacketLayout.push (HeadPacketLayout.addLogical records) context) := by
  cases plain <;> cases plan <;> cases context <;> try exact False.elim represented
  · trivial
  · exact logical markerId blocks payload reverse _ _ _ represented records

theorem realJoin (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (records : List ρ)
    (leftPlain rightPlain : ProjectionLocal.Projected α ρ) (leftPlan rightPlan : HeadPacketRepair.Layout κ)
    (leftContext rightContext : HeadPacketLayout.Layout κ α ρ ι)
    (leftRep : Layout markerId blocks payload reverse leftPlain leftPlan leftContext)
    (rightRep : Layout markerId blocks payload reverse rightPlain rightPlan rightContext) :
    Layout markerId blocks payload reverse
      (ProjectionLocal.decorate records (ProjectionLocal.join
        (if reverse then rightPlain else leftPlain) (if reverse then leftPlain else rightPlain)))
      (HeadPacketRepair.realJoin reverse leftPlan rightPlan)
      (HeadPacketLayout.realJoin markerId records leftContext rightContext) := by
  cases leftPlain <;> cases leftPlan <;> cases leftContext <;> try exact False.elim leftRep
  all_goals cases rightPlain <;> cases rightPlan <;> cases rightContext <;> try exact False.elim rightRep
  · cases reverse <;> trivial
  · cases reverse <;> exact logical markerId blocks payload _ _ _ _ rightRep records
  · cases reverse <;> exact logical markerId blocks payload _ _ _ _ leftRep records
  · cases reverse <;>
      simpa only [ProjectionLocal.decorate,ProjectionLocal.join,Option.map_some,Source.setRoot,Source.rootRecord,List.append_nil,
        Bool.false_eq_true,if_false,if_true,Layout,HeadPacketRepair.realJoin,HeadPacketLayout.realJoin] using
        fork markerId blocks payload _ records _ _ _ _ _ _ leftRep rightRep

theorem block (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool) (bits : κ → Bool) (key : κ)
    (tagged : Option (Tagged α ρ ι)) (oldParent : Option ι)
    (present : bits key = tagged.isSome)
    (blockView : ∀ tree, tagged = some tree → blocks key = routing payload reverse oldParent tree)
    (ordinary : ∀ tree, tagged = some tree → tree.rootRecord.1 ≠ markerId) :
    Layout markerId blocks payload reverse (tagged.map (Source.mapRecords Prod.snd))
      (HeadPacketRepair.block bits key) (HeadPacketLayout.block bits key) := by
  cases tagged with
  | none => simp only [HeadPacketRepair.block,HeadPacketLayout.block,present,Option.isSome_none,Bool.false_eq_true,if_false]; trivial
  | some tree =>
    simp only [HeadPacketRepair.block,HeadPacketLayout.block,present,Option.isSome_some,if_true,Option.map_some,Layout]
    have represented := opaque_block markerId blocks payload reverse key oldParent tree [] (blockView tree rfl) (ordinary tree rfl)
    have same : (tree.mapRecords Prod.snd).setRoot ([] ++ (tree.mapRecords Prod.snd).rootRecord) = tree.mapRecords Prod.snd := by
      cases tree <;> rfl
    rw [same] at represented
    exact represented

end ChaCha.Paper20261030.CanonicalRepairedRouting
