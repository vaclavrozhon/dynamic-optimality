import TangoSquared.Paper20261030.StructuralRotationReads

/-!
# Structural annotations at arbitrary source cursor positions

The current record's parent field and every ancestor's child descriptor
are obtained from the same whole annotated tree. Adjacent navigation costs
one actual step. After a rooted rearrangement preserving the color mask,
only the immediate external parent's child descriptor can have changed;
repairing it costs at most four reached-pointer operations.
-/

namespace TangoSquared.Paper20261030.Structural

open ColoredStorage SourcePointer

variable {α ρ ι C : Type*} [DecidableEq C]

def parentId (identifier : ρ → ι) : List (Frame α ρ) → Option ι
  | [] => none
  | .left record _ :: _ => some (identifier record)
  | .right _ record :: _ => some (identifier record)

def frames (identifier : ρ → ι) (color : α → C) (focus : Source α ρ) :
    List (Frame α ρ) → List (Frame α (ρ × Fields ι C))
  | [] => []
  | .left record sibling :: rest =>
      .left (record,fields identifier color (parentId identifier rest) (.fork record focus sibling))
        (annotate identifier color (some (identifier record)) sibling) ::
      frames identifier color (.fork record focus sibling) rest
  | .right sibling record :: rest =>
      .right (annotate identifier color (some (identifier record)) sibling)
        (record,fields identifier color (parentId identifier rest) (.fork record sibling focus)) ::
      frames identifier color (.fork record sibling focus) rest

def cursor (identifier : ρ → ι) (color : α → C) (source : Cursor α ρ) : Cursor α (ρ × Fields ι C) :=
  ⟨annotate identifier color (parentId identifier source.ancestors) source.focus,
    frames identifier color source.focus source.ancestors⟩

theorem plug_frames (identifier : ρ → ι) (color : α → C) (focus : Source α ρ)
    (outside : List (Frame α ρ)) :
    plug (annotate identifier color (parentId identifier outside) focus) (frames identifier color focus outside) =
      annotate identifier color none (plug focus outside) := by
  induction outside generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
    cases frame with
    | left record sibling => exact ih (.fork record focus sibling)
    | right sibling record => exact ih (.fork record sibling focus)

theorem cursor_tree (identifier : ρ → ι) (color : α → C) (source : Cursor α ρ) :
    (cursor identifier color source).tree = annotate identifier color none source.tree :=
  plug_frames identifier color source.focus source.ancestors

theorem move (identifier : ρ → ι) (color : α → C) {before after : Cursor α ρ}
    (navigation : Move before after) :
    Move (cursor identifier color before) (cursor identifier color after) := by
  cases navigation
  · exact .left _ _ _ _
  · exact .right _ _ _ _
  · exact .upLeft _ _ _ _
  · exact .upRight _ _ _ _

theorem frames_congr (identifier : ρ → ι) (color : α → C) {before after : Source α ρ}
    (sameId : identifier before.rootRecord = identifier after.rootRecord)
    (sameColors : before.support color = after.support color) (outside : List (Frame α ρ)) :
    frames identifier color before outside = frames identifier color after outside := by
  induction outside generalizing before after with
  | nil => rfl
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      have tail := ih (before := .fork record before sibling) (after := .fork record after sibling) rfl
        (by simp only [Source.support,sameColors])
      simp only [frames,fields,descriptor,Source.support,sameId,sameColors,tail]
    | right sibling record =>
      have tail := ih (before := .fork record sibling before) (after := .fork record sibling after) rfl
        (by simp only [Source.support,sameColors])
      simp only [frames,fields,descriptor,Source.support,sameId,sameColors,tail]

theorem repair_parent (identifier : ρ → ι) (color : α → C) (before after : Source α ρ)
    (sameColors : before.support color = after.support color) (outside : List (Frame α ρ)) :
    ∃ reads cost,
      Trace ⟨annotate identifier color (parentId identifier outside) after,frames identifier color before outside⟩
        reads (cursor identifier color ⟨after,outside⟩) cost ∧ cost ≤ 4 := by
  cases outside with
  | nil => exact ⟨[],0,.nil _,by decide⟩
  | cons frame rest =>
    cases frame with
    | left record sibling =>
      let A := annotate identifier color (some (identifier record)) after
      let R := annotate identifier color (some (identifier record)) sibling
      let old := (record,fields identifier color (parentId identifier rest) (.fork record before sibling))
      let fresh := (record,fields identifier color (parentId identifier rest) (.fork record after sibling))
      have tail := frames_congr identifier color (before := .fork record before sibling)
        (after := .fork record after sibling) rfl (by simp only [Source.support,sameColors]) rest
      let rest' := frames identifier color (.fork record after sibling) rest
      have trace : Trace ⟨A,.left old R :: rest'⟩ [old] ⟨A,.left fresh R :: rest'⟩ 4 :=
        .step (.upLeft _ _ _ _) (.read (.step (.write _ fresh _) (.step (.left _ _ _ _) (.nil _))))
      refine ⟨[old],4,?_,le_rfl⟩
      simpa only [A,R,old,fresh,rest',cursor,frames,parentId,tail] using trace
    | right sibling record =>
      let A := annotate identifier color (some (identifier record)) after
      let L := annotate identifier color (some (identifier record)) sibling
      let old := (record,fields identifier color (parentId identifier rest) (.fork record sibling before))
      let fresh := (record,fields identifier color (parentId identifier rest) (.fork record sibling after))
      have tail := frames_congr identifier color (before := .fork record sibling before)
        (after := .fork record sibling after) rfl (by simp only [Source.support,sameColors]) rest
      let rest' := frames identifier color (.fork record sibling after) rest
      have trace : Trace ⟨A,.right L old :: rest'⟩ [old] ⟨A,.right L fresh :: rest'⟩ 4 :=
        .step (.upRight _ _ _ _) (.read (.step (.write _ fresh _) (.step (.right _ _ _ _) (.nil _))))
      refine ⟨[old],4,?_,le_rfl⟩
      simpa only [A,L,old,fresh,rest',cursor,frames,parentId,tail] using trace

theorem lift_rearrangement (identifier : ρ → ι) (color : α → C) (before after : Source α ρ)
    (sameColors : before.support color = after.support color) (budget : Nat)
    (kernel : ∀ parent, Rearranges (annotate identifier color parent before)
      (annotate identifier color parent after) budget) (outside : List (Frame α ρ)) :
    ∃ reads cost, Trace (cursor identifier color ⟨before,outside⟩) reads
      (cursor identifier color ⟨after,outside⟩) cost ∧ cost ≤ budget+4 := by
  obtain ⟨firstReads,firstCost,first,firstBound⟩ := kernel (parentId identifier outside)
    (frames identifier color before outside)
  obtain ⟨lastReads,lastCost,last,lastBound⟩ := repair_parent identifier color before after sameColors outside
  exact ⟨_,_,first.append last,by omega⟩

end TangoSquared.Paper20261030.Structural
