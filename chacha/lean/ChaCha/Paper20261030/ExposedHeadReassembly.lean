import ChaCha.Paper20261030.PhysicalPackedViews

/-!
# Physical head exchange with all exposed record prefixes retained

Six routing blocks and two original bottom keys form the unchanged ordered
blocks of the exchange. Connector records, virtual headers, and attachment
markers are arbitrary explicit prefixes. The kernel includes their removal
and installation, including prefixes at roots of absent routing wings.
-/

namespace ChaCha.Paper20261030.OrderedContext

open ColoredStorage ProjectionLocal RouterProjection

variable {ι α ρ : Type*}

def Contextual (blocks : ι → Projected α ρ) (word : List ι) (source : Projected α ρ) : Prop :=
  ∃ context : Source ι (List ρ), context.shape.leaves = word ∧ decorated blocks context = source

theorem Contextual.block (blocks : ι → Projected α ρ) (i : ι) : Contextual blocks [i] (blocks i) :=
  ⟨.leaf i [],rfl,decorate_nil _⟩

theorem Contextual.join {blocks : ι → Projected α ρ} {a b : List ι} {left right : Projected α ρ}
    (hl : Contextual blocks a left) (hr : Contextual blocks b right) :
    Contextual blocks (a++b) (ProjectionLocal.join left right) := by
  obtain ⟨l,hl,el⟩ := hl
  obtain ⟨r,hr,er⟩ := hr
  refine ⟨.fork [] l r,by simp [Source.shape,Router.leaves,hl,hr],?_⟩
  simp only [decorated,decorate_nil,el,er]

theorem decorate_append (first second : List ρ) (source : Projected α ρ) :
    decorate (first++second) source = decorate first (decorate second source) := by
  cases source with
  | none => rfl
  | some source => cases source <;> simp [decorate,Source.rootRecord,Source.setRoot,List.append_assoc]

theorem Contextual.decorate {blocks : ι → Projected α ρ} {word : List ι} {source : Projected α ρ}
    (h : Contextual blocks word source) (records : List ρ) : Contextual blocks word (decorate records source) := by
  obtain ⟨context,wordEq,sourceEq⟩ := h
  refine ⟨context.setRoot (records++context.rootRecord),?_,?_⟩
  · cases context <;> exact wordEq
  · rw [← sourceEq]
    cases context <;> exact decorate_append _ _ _

theorem Contextual.reassemble {blocks : ι → Projected α ρ} {word : List ι}
    {before after : Projected α ρ} (hb : Contextual blocks word before) (ha : Contextual blocks word after) :
    Rearranges before after (36*word.length) := by
  obtain ⟨b,wb,eb⟩ := hb
  obtain ⟨a,wa,ea⟩ := ha
  rw [← eb,← ea]
  exact reassemble_decorated blocks b a (wb.trans wa.symm) word.length (congrArg List.length wb)

end ChaCha.Paper20261030.OrderedContext

namespace ChaCha.Paper20261030.HeadBlocks

open ColoredStorage ProjectionLocal OrderedContext

variable {α ρ : Type*}

structure ActiveRecords (ρ : Type*) where
  lowerLeft : List ρ
  lowerRight : List ρ
  upperLeft : List ρ
  upperRight : List ρ
  bottom : List ρ
  attachment : List ρ

structure DormantRecords (ρ : Type*) where
  left : List ρ
  right : List ρ
  bottom : List ρ

def dormantView (left bottom right : Projected α ρ) (records : DormantRecords ρ) : Projected α ρ :=
  join (join (decorate records.left left) (decorate records.bottom bottom)) (decorate records.right right)

def activeView (prefixLeft prefixRight tailLeft bottom tailRight boundary : Projected α ρ)
    (direction : Bool) (records : ActiveRecords ρ) : Projected α ρ :=
  let child := decorate records.attachment boundary
  let left := if direction then join child tailLeft else tailLeft
  let right := if direction then tailRight else join tailRight child
  join (join
    (decorate records.lowerLeft (join prefixLeft (decorate records.upperLeft left)))
    (decorate records.bottom bottom))
    (decorate records.lowerRight (join (decorate records.upperRight right) prefixRight))

def exposedBefore (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (active : ActiveRecords ρ) (dormant : DormantRecords ρ) : Projected α ρ :=
  activeView (blocks 0) (blocks 7) (blocks 1) (blocks 2) (blocks 3)
    (dormantView (blocks 4) (blocks 5) (blocks 6) dormant) direction active

def exposedAfter (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (active : ActiveRecords ρ) (dormant : DormantRecords ρ) : Projected α ρ :=
  activeView (blocks 0) (blocks 7) (blocks 4) (blocks 5) (blocks 6)
    (dormantView (blocks 1) (blocks 2) (blocks 3) dormant) (!direction) active

def exposedOrder : Bool → List (Fin 8)
  | false => [0,1,2,3,4,5,6,7]
  | true => [0,4,5,6,1,2,3,7]

theorem dormant_context {ι : Type*} {blocks : ι → Projected α ρ}
    {left bottom right : Projected α ρ} {l b r : List ι}
    (hl : Contextual blocks l left) (hb : Contextual blocks b bottom) (hr : Contextual blocks r right)
    (records : DormantRecords ρ) : Contextual blocks ((l++b)++r) (dormantView left bottom right records) :=
  ((hl.decorate records.left).join (hb.decorate records.bottom)).join (hr.decorate records.right)

theorem exposed_before_context (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (active : ActiveRecords ρ) (dormant : DormantRecords ρ) :
    Contextual blocks (exposedOrder direction) (exposedBefore blocks direction active dormant) := by
  have h (i : Fin 8) := Contextual.block blocks i
  have incoming := dormant_context (h 4) (h 5) (h 6) dormant
  cases direction
  · exact (((h 0).join ((h 1).decorate active.upperLeft)).decorate active.lowerLeft |>.join
      ((h 2).decorate active.bottom)).join
        ((((h 3).join (incoming.decorate active.attachment)).decorate active.upperRight |>.join
          (h 7)).decorate active.lowerRight)
  · exact (((h 0).join (((incoming.decorate active.attachment).join (h 1)).decorate active.upperLeft)).decorate
      active.lowerLeft |>.join ((h 2).decorate active.bottom)).join
        ((((h 3).decorate active.upperRight).join (h 7)).decorate active.lowerRight)

theorem exposed_after_context (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (active : ActiveRecords ρ) (dormant : DormantRecords ρ) :
    Contextual blocks (exposedOrder direction) (exposedAfter blocks direction active dormant) := by
  have h (i : Fin 8) := Contextual.block blocks i
  have old := dormant_context (h 1) (h 2) (h 3) dormant
  cases direction
  · exact (((h 0).join (((old.decorate active.attachment).join (h 4)).decorate active.upperLeft)).decorate
      active.lowerLeft |>.join ((h 5).decorate active.bottom)).join
        ((((h 6).decorate active.upperRight).join (h 7)).decorate active.lowerRight)
  · exact (((h 0).join ((h 4).decorate active.upperLeft)).decorate active.lowerLeft |>.join
      ((h 5).decorate active.bottom)).join
        ((((h 6).join (old.decorate active.attachment)).decorate active.upperRight |>.join
          (h 7)).decorate active.lowerRight)

theorem exposed_head_reassembly (blocks : Fin 8 → Projected α ρ) (direction : Bool)
    (oldActive newActive : ActiveRecords ρ) (oldDormant newDormant : DormantRecords ρ) :
    Rearranges (exposedBefore blocks direction oldActive oldDormant)
      (exposedAfter blocks direction newActive newDormant) 288 := by
  have result := (exposed_before_context blocks direction oldActive oldDormant).reassemble
    (exposed_after_context blocks direction newActive newDormant)
  cases direction <;> exact result

end ChaCha.Paper20261030.HeadBlocks
