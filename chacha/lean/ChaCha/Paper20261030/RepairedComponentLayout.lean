import ChaCha.Paper20261030.CanonicalRepairedRouting

set_option autoImplicit false

/-!
# Composing repaired component pieces across primary connectors

Unlike a real routing fork, a primary connector has an empty packet and
starts both component pieces with no routing parent. Optional layouts
suppress absent wings. The bottom keeps its raw virtual header and its
opaque payload exactly. These rules compose semantic predicates on the
actual repaired output, including canonical routing witnesses.
-/

namespace ChaCha.Paper20261030.RepairedComponentLayout

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers MixedPacketRepair
open CanonicalPacketLayerViews

variable {κ α β ρ ι : Type*}

abbrev View (β α ρ ι : Type*) := Option (Source β (Packet α ρ ι))

def Represents (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) :
    HeadPacketRepair.Layout κ → HeadPacketLayout.Layout κ α ρ ι → (View β α ρ ι → Prop) → Prop
  | none,none,predicate => predicate none
  | some plan,some context,predicate => TreeMatches plan context ∧
      ∀ source, Reached.Repacked blocks context source →
        SourceRecordPredicate.Holds (PacketAlignment.Predicate markerId) source →
        predicate (some ((output plan none source).mapRecords Prod.snd))
  | _,_,_ => False

theorem weaken (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (p q : View β α ρ ι → Prop) (represented : Represents markerId blocks plan context p)
    (implies : ∀ view, p view → q view) : Represents markerId blocks plan context q := by
  cases plan <;> cases context <;> try exact False.elim represented
  · exact implies none represented
  · exact ⟨represented.1,fun source repacked aligned => implies _ (represented.2 source repacked aligned)⟩

theorem primaryJoin (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (leftPlan rightPlan : HeadPacketRepair.Layout κ) (leftContext rightContext : HeadPacketLayout.Layout κ α ρ ι)
    (p q : View β α ρ ι → Prop)
    (leftRep : Represents markerId blocks leftPlan leftContext p)
    (rightRep : Represents markerId blocks rightPlan rightContext q) :
    Represents markerId blocks (HeadPacketRepair.primaryJoin leftPlan rightPlan)
      (HeadPacketLayout.primaryJoin leftContext rightContext)
      (fun view => ∃ left right, p left ∧ q right ∧ view = ProjectionLocal.join left right) := by
  cases leftPlan <;> cases leftContext <;> try exact False.elim leftRep
  all_goals cases rightPlan <;> cases rightContext <;> try exact False.elim rightRep
  · exact ⟨none,none,leftRep,rightRep,rfl⟩
  · refine ⟨rightRep.1,?_⟩
    intro source repacked aligned
    exact ⟨none,_,leftRep,rightRep.2 source repacked aligned,rfl⟩
  · refine ⟨leftRep.1,?_⟩
    intro source repacked aligned
    exact ⟨_,none,leftRep.2 source repacked aligned,rightRep,rfl⟩
  · refine ⟨.fork _ _ _ _ _ _ .base leftRep.1 rightRep.1,?_⟩
    intro source repacked aligned
    cases repacked with
    | fork _ _ _ l r id hl hr =>
      obtain ⟨_,leftAligned,rightAligned⟩ := (SourceRecordPredicate.fork _ _ _ _).mp aligned
      exact ⟨_,_,leftRep.2 l hl leftAligned,rightRep.2 r hr rightAligned,rfl⟩

private theorem root_set {σ : Type*} (source : Source β σ) (record : σ) :
    (source.setRoot record).rootRecord = record := by cases source <;> rfl

private theorem set_set {σ : Type*} (source : Source β σ) (first last : σ) :
    (source.setRoot first).setRoot last = source.setRoot last := by cases source <;> rfl

theorem bottom (markerId : ι) (blocks : κ → Source β (Packet α ρ ι)) (key : κ) (header : Packet α ρ ι) :
    Represents markerId blocks (HeadPacketRepair.bottom key header.length) (HeadPacketLayout.bottom key header)
      (fun view => view = some ((blocks key).setRoot (header++(blocks key).rootRecord))) := by
  refine ⟨.leaf key _ _ (.raw header _ _ .base),?_⟩
  intro source repacked aligned
  cases repacked with
  | leaf _ _ block erases =>
    simp only [output,cell,rebuilt,root_set,edit,List.take_left,List.drop_left,List.take_append_drop,
      set_set,Source.mapRecords_setRoot,erases]

theorem routing (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : ProjectionLocal.Projected α ρ) (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (represented : CanonicalRepairedRouting.Layout markerId blocks payload reverse plain plan context) :
    Represents markerId blocks plan context (fun view => ∃ tagged : Option (Tagged α ρ ι),
      tagged.map (Source.mapRecords Prod.snd) = plain ∧ view = tagged.map (routing payload reverse none)) := by
  cases plain <;> cases plan <;> cases context <;> try exact False.elim represented
  · exact ⟨none,rfl,rfl⟩
  · refine ⟨represented.1,?_⟩
    intro source repacked aligned
    obtain ⟨tagged,erases,view,id⟩ := represented.2.2 none source repacked aligned
    exact ⟨some tagged,congrArg some erases,congrArg some view⟩

end ChaCha.Paper20261030.RepairedComponentLayout
