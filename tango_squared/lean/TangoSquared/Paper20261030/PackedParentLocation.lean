import TangoSquared.Paper20261030.PackedNavigationDecision

/-! The parent-record location claim in the local simulation lemma.
For at least one color, the logical parent's record is at the current
physical finger or its immediate physical parent. This is a structural
location theorem; the bounded local observation tour is separate.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

open SourcePointer SourceLocalProgram

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

omit [DecidableEq α] in
theorem up_of_left {before after : Cursor α ρ} (moved : navigate .left before = some after) :
    navigate .up after = some before := by
  rcases before with ⟨focus,outside⟩
  cases focus with
  | leaf => simp [navigate] at moved
  | fork => cases Option.some.inj moved; rfl

omit [DecidableEq α] in
theorem up_of_right {before after : Cursor α ρ} (moved : navigate .right before = some after) :
    navigate .up after = some before := by
  rcases before with ⟨focus,outside⟩
  cases focus with
  | leaf => simp [navigate] at moved
  | fork => cases Option.some.inj moved; rfl

theorem parent_location_left (color : α → C) (l r : Source α ρ) (record : ρ) (outside)
    {physical : Cursor α (List ρ)}
    (represented : Represents color (Source.rootOwner color (.fork record l r))
      ⟨l,.left record r::outside⟩ physical) :
    (Represents color (Source.rootOwner color (.fork record l r)) ⟨.fork record l r,outside⟩ physical) ∨
    (∃ parent, navigate .up physical = some parent ∧
      Represents color (Source.rootOwner color (.fork record l r)) ⟨.fork record l r,outside⟩ parent) := by
  let q := Source.rootOwner color (.fork record l r)
  obtain ⟨parent,_,_,_,parentRep⟩ := navigation color q represented (SourcePointer.Move.upLeft l r record outside)
  by_cases active : q ∈ l.support color ∧ q ∈ r.support color
  · obtain ⟨child,moved,childRep⟩ := left_active color q l r record outside active parentRep
    have equal := Represents.unique color q ⟨l,.left record r::outside⟩ childRep represented
    subst child
    exact Or.inr ⟨parent,up_of_left moved,parentRep⟩
  · have idle : q ∉ l.support color ∨ q ∉ r.support color := by
      by_cases left : q ∈ l.support color
      · exact Or.inr (fun right => active ⟨left,right⟩)
      · exact Or.inl left
    have childRep := left_idle color q l r record outside idle parentRep
    have equal := Represents.unique color q ⟨l,.left record r::outside⟩ childRep represented
    subst parent
    exact Or.inl parentRep

theorem parent_location_right (color : α → C) (l r : Source α ρ) (record : ρ) (outside)
    {physical : Cursor α (List ρ)}
    (represented : Represents color (Source.rootOwner color (.fork record l r))
      ⟨r,.right l record::outside⟩ physical) :
    (Represents color (Source.rootOwner color (.fork record l r)) ⟨.fork record l r,outside⟩ physical) ∨
    (∃ parent, navigate .up physical = some parent ∧
      Represents color (Source.rootOwner color (.fork record l r)) ⟨.fork record l r,outside⟩ parent) := by
  let q := Source.rootOwner color (.fork record l r)
  obtain ⟨parent,_,_,_,parentRep⟩ := navigation color q represented (SourcePointer.Move.upRight l r record outside)
  by_cases active : q ∈ l.support color ∧ q ∈ r.support color
  · obtain ⟨child,moved,childRep⟩ := right_active color q l r record outside active parentRep
    have equal := Represents.unique color q ⟨r,.right l record::outside⟩ childRep represented
    subst child
    exact Or.inr ⟨parent,up_of_right moved,parentRep⟩
  · have idle : q ∉ l.support color ∨ q ∉ r.support color := by
      by_cases left : q ∈ l.support color
      · exact Or.inr (fun right => active ⟨left,right⟩)
      · exact Or.inl left
    have childRep := right_idle color q l r record outside idle parentRep
    have equal := Represents.unique color q ⟨r,.right l record::outside⟩ childRep represented
    subst parent
    exact Or.inl parentRep

/-- A candidate reached by an observation tour contains only actual
source records; its position need not represent the current logical cursor. -/
theorem record_mem_of_packed (color : α → C) (q : C) (source : Source α ρ)
    (physical : Cursor α (List ρ)) (packedTree : packed color q source = some physical.tree)
    {record : ρ} (member : record ∈ physical.focus.rootRecord) : record ∈ source.records := by
  have full := stored_records_focus physical.focus physical.ancestors (Source.rootRecords_mem _ member)
  change record ∈ physical.tree.toStored.records at full
  rw [packed_toStored color q source packedTree] at full
  exact pack_records_mem color q source full

theorem forest_parent_record [Fintype C] (color : α → C) (right : Bool)
    (l r : Source α ρ) (record : ρ) (outside)
    (forest : ProjectionForest.State C α ρ)
    (represented : ProjectionForest.Represents color
      (if right then ⟨r,.right l record::outside⟩ else ⟨l,.left record r::outside⟩) forest) :
    ∃ q physical, forest q = some physical ∧
      ((record ∈ physical.focus.rootRecord ∧ physical.focus.rootRecord.length ≤ Fintype.card C) ∨
        ∃ parent, navigate .up physical = some parent ∧ record ∈ parent.focus.rootRecord ∧
          parent.focus.rootRecord.length ≤ Fintype.card C) := by
  let q := Source.rootOwner color (.fork record l r)
  have inWhole : q ∈ (Cursor.tree ⟨.fork record l r,outside⟩).support color :=
    ProjectionForest.support_focus color _ outside (Source.rootOwner_mem color (.fork record l r))
  have atRep := represented q
  cases location : forest q with
  | none =>
    rw [location] at atRep
    cases right <;> exact False.elim (atRep inWhole)
  | some physical =>
    rw [location] at atRep
    have place : Represents color q ⟨.fork record l r,outside⟩ physical ∨
        ∃ parent, navigate .up physical = some parent ∧ Represents color q ⟨.fork record l r,outside⟩ parent := by
      cases right with
      | false => exact parent_location_left color l r record outside atRep
      | true => exact parent_location_right color l r record outside atRep
    refine ⟨q,physical,location,?_⟩
    rcases place with current | ⟨parent,moved,parentRep⟩
    · obtain ⟨_,member,bounded⟩ := read_record color ⟨.fork record l r,outside⟩ current
      exact Or.inl ⟨member,bounded⟩
    · obtain ⟨_,member,bounded⟩ := read_record color ⟨.fork record l r,outside⟩ parentRep
      exact Or.inr ⟨parent,moved,member,bounded⟩

end TangoSquared.Paper20261030.ColoredStorage
