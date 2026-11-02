import ChaCha.Paper20261030.CanonicalRepairedPayloadRouting

set_option autoImplicit false

/-! Optional routing layouts with semantic payload predicates. The port
sets record exactly which attached components belong to a piece; their
disjointness justifies merging the proof-level payload witnesses. -/

namespace ChaCha.Paper20261030.RepairedPayloadLayouts

open ColoredStorage SourcePointer Structural PhysicalPacketStaging PacketLayers
open CanonicalPacketLayerViews MixedPacketRepair

variable {κ α β ρ ι : Type*}

def ports : ProjectionLocal.Projected α ρ → List α
  | none => []
  | some tree => tree.shape.leaves

theorem ports_decorate (records : List ρ) (plain : ProjectionLocal.Projected α ρ) :
    ports (ProjectionLocal.decorate records plain) = ports plain := by
  cases plain with
  | none => rfl
  | some tree => exact congrArg RouterProjection.Router.leaves (source_setRoot_shape tree _)

theorem ports_join (left right : ProjectionLocal.Projected α ρ) :
    ports (ProjectionLocal.join left right) = ports left ++ ports right := by
  cases left <;> cases right <;> simp only [ProjectionLocal.join,ports,Source.shape,RouterProjection.Router.leaves,List.append_nil,List.nil_append]

def Separate (left right : ProjectionLocal.Projected α ρ) : Prop :=
  ∀ key, key ∈ ports left → key ∈ ports right → False

theorem Separate.symm {left right : ProjectionLocal.Projected α ρ} (separate : Separate left right) : Separate right left :=
  fun key hl hr => separate key hr hl

theorem Separate.decorate_left {left right : ProjectionLocal.Projected α ρ} (separate : Separate left right) (records : List ρ) :
    Separate (ProjectionLocal.decorate records left) right := by
  intro key hl hr
  rw [ports_decorate] at hl
  exact separate key hl hr

theorem Separate.decorate_right {left right : ProjectionLocal.Projected α ρ} (separate : Separate left right) (records : List ρ) :
    Separate left (ProjectionLocal.decorate records right) := (separate.symm.decorate_left records).symm

theorem Separate.join_right {left first last : ProjectionLocal.Projected α ρ}
    (hf : Separate left first) (hl : Separate left last) : Separate left (ProjectionLocal.join first last) := by
  intro key member both
  rw [ports_join] at both
  rcases List.mem_append.mp both with first | last
  · exact hf key member first
  · exact hl key member last

theorem singleton_separate (key : α) (records : List ρ) (plain : ProjectionLocal.Projected α ρ)
    (absent : key ∉ ports plain) : Separate (some (.leaf key records)) plain := by
  intro other member inside
  have same : other = key := by simpa only [ports,Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using member
  subst other
  exact absent inside

def Layout (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool) :
    ProjectionLocal.Projected α ρ → HeadPacketRepair.Layout κ → HeadPacketLayout.Layout κ α ρ ι → Prop
  | none,none,none => True
  | some plain,some plan,some context => CanonicalRepairedPayloadRouting.Represents markerId blocks good reverse plain plan context
  | _,_,_ => False

theorem fixed (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (payload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : ProjectionLocal.Projected α ρ) (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (represented : CanonicalRepairedRouting.Layout markerId blocks payload reverse plain plan context)
    (valid : ∀ key ∈ ports plain, good key (payload key)) : Layout markerId blocks good reverse plain plan context := by
  cases plain <;> cases plan <;> cases context <;> try exact False.elim represented
  · trivial
  · exact CanonicalRepairedPayloadRouting.fixed markerId blocks good payload reverse _ _ _ represented valid

theorem logical (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool)
    (plain : ProjectionLocal.Projected α ρ) (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (represented : Layout markerId blocks good reverse plain plan context) (records : List ρ) :
    Layout markerId blocks good reverse (ProjectionLocal.decorate records plain) plan
      (HeadPacketLayout.push (HeadPacketLayout.addLogical records) context) := by
  cases plain <;> cases plan <;> cases context <;> try exact False.elim represented
  · trivial
  · exact CanonicalRepairedPayloadRouting.logical markerId blocks good reverse _ _ _ represented records

theorem realJoin (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool) (records : List ρ)
    (leftPlain rightPlain : ProjectionLocal.Projected α ρ) (leftPlan rightPlan : HeadPacketRepair.Layout κ)
    (leftContext rightContext : HeadPacketLayout.Layout κ α ρ ι) (separate : Separate leftPlain rightPlain)
    (leftRep : Layout markerId blocks good reverse leftPlain leftPlan leftContext)
    (rightRep : Layout markerId blocks good reverse rightPlain rightPlan rightContext) :
    Layout markerId blocks good reverse
      (ProjectionLocal.decorate records (ProjectionLocal.join
        (if reverse then rightPlain else leftPlain) (if reverse then leftPlain else rightPlain)))
      (HeadPacketRepair.realJoin reverse leftPlan rightPlan)
      (HeadPacketLayout.realJoin markerId records leftContext rightContext) := by
  cases leftPlain <;> cases leftPlan <;> cases leftContext <;> try exact False.elim leftRep
  all_goals cases rightPlain <;> cases rightPlan <;> cases rightContext <;> try exact False.elim rightRep
  · cases reverse <;> trivial
  · cases reverse <;> exact CanonicalRepairedPayloadRouting.logical markerId blocks good _ _ _ _ rightRep records
  · cases reverse <;> exact CanonicalRepairedPayloadRouting.logical markerId blocks good _ _ _ _ leftRep records
  · cases reverse <;>
      simpa only [ProjectionLocal.decorate,ProjectionLocal.join,Option.map_some,Source.setRoot,Source.rootRecord,List.append_nil,
        Bool.false_eq_true,if_false,if_true,Layout,HeadPacketRepair.realJoin,HeadPacketLayout.realJoin] using
        CanonicalRepairedPayloadRouting.fork markerId blocks good _ records _ _ _ _ _ _ separate leftRep rightRep

theorem attachment (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (reverse : Bool) (key : α) (record : ρ)
    (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (predicate : RepairedComponentLayout.View β α ρ ι → Prop)
    (childRep : RepairedComponentLayout.Represents markerId blocks plan context predicate)
    (present : ¬ predicate none) (accepts : ∀ body, predicate (some body) → good key body) :
    Layout markerId blocks good reverse (some (.leaf key [record]))
      (HeadPacketRepair.attachment plan) (HeadPacketLayout.attachment markerId record context) := by
  cases plan <;> cases context <;> try exact False.elim childRep
  · exact False.elim (present childRep)
  · apply CanonicalRepairedPayloadRouting.attachment markerId blocks good reverse key record
    apply RepairedComponentLayout.weaken markerId blocks _ _ _ _ childRep
    intro view valid
    cases view with
    | none => exact False.elim (present valid)
    | some body => exact ⟨body,accepts body valid,rfl⟩

theorem component_piece (markerId : ι) (blocks : κ → Source β (Packet α ρ ι))
    (good : α → Source β (Packet α ρ ι) → Prop) (defaultPayload : α → Source β (Packet α ρ ι)) (reverse : Bool)
    (plain : ProjectionLocal.Projected α ρ) (plan : HeadPacketRepair.Layout κ) (context : HeadPacketLayout.Layout κ α ρ ι)
    (represented : Layout markerId blocks good reverse plain plan context) :
    RepairedComponentLayout.Represents markerId blocks plan context
      (fun view => ∃ (tagged : Option (Tagged α ρ ι)) (payload : α → Source β (Packet α ρ ι)),
        tagged.map (Source.mapRecords Prod.snd) = plain ∧ (∀ key ∈ ports plain, good key (payload key)) ∧
        view = tagged.map (routing payload reverse none)) := by
  cases plain <;> cases plan <;> cases context <;> try exact False.elim represented
  · exact ⟨none,defaultPayload,rfl,(by intro key member; cases member),rfl⟩
  · refine ⟨represented.1,?_⟩
    intro source repacked aligned
    obtain ⟨tagged,payload,erases,valid,view,id⟩ := represented.2.2 none source repacked aligned
    exact ⟨some tagged,payload,congrArg some erases,valid,congrArg some view⟩

end ChaCha.Paper20261030.RepairedPayloadLayouts
