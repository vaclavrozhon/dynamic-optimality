import ChaCha.Paper20261030.PackedCursorContext

/-!
# Reading and writing the record at a represented source cursor

The owning color's active cursor reaches a bounded record list containing
the current source record. Updating that record is a read and write at
this physical vertex. The enclosing packed tree and the represented
cursor are restored exactly; all other color trees are unchanged.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer ProjectionLocal RouterProjection

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem packed_toStored (color : α → C) (q : C) (source : Source α ρ)
    {actual : Source α (List ρ)} (h : packed color q source = some actual) :
    actual.toStored = pack color q source := by
  have hf : Router.Full (pack color q source).shape := by
    rw [pack_shape]; exact Router.full_prune _ _
  have he := (pack color q source).toSource_roundtrip hf
  change storedOption (packed color q source) = _ at he
  simpa only [h,storedOption] using he

theorem packed_exists (color : α → C) (q : C) (source : Source α ρ)
    (hq : q ∈ source.support color) : ∃ actual, packed color q source = some actual := by
  have hf : Router.Full (pack color q source).shape := by
    rw [pack_shape]; exact Router.full_prune _ _
  obtain ⟨actual,he,_⟩ := Stored.toSource_exists _ hf ((pack_nonempty color q source).mpr hq)
  exact ⟨actual,he⟩

theorem Source.rootOwner_mem (color : α → C) (source : Source α ρ) :
    source.rootOwner color ∈ source.support color := by
  cases source with
  | leaf key record => simp [Source.rootOwner,Source.support]
  | fork record l r => exact owner_mem color l r

theorem Source.support_setRoot (color : α → C) (source : Source α ρ) (fresh : ρ) :
    (source.setRoot fresh).support color = source.support color := by cases source <;> rfl

theorem packed_root_head (color : α → C) (source : Source α ρ)
    {actual : Source α (List ρ)}
    (h : packed color (source.rootOwner color) source = some actual) :
    ∃ tail, actual.rootRecord = source.rootRecord :: tail := by
  obtain ⟨tail,he⟩ := pack_root_head color source
  have hr := congrArg Stored.rootRecords (packed_toStored color _ source h)
  rw [Source.toStored_rootRecords,he] at hr
  exact ⟨tail,hr⟩

theorem record_at_cursor (color : α → C) (source : Cursor α ρ)
    {physical : Cursor α (List ρ)}
    (h : Represents color (source.focus.rootOwner color) source physical) :
    ∃ extras tail, physical.focus.rootRecord = extras ++ source.focus.rootRecord :: tail := by
  obtain ⟨actual,ha⟩ := packed_exists color _ source.focus (Source.rootOwner_mem color _)
  obtain ⟨extras,rest,hbefore,_,hframes⟩ := packed_cursor_context color _ rfl ha ha source.ancestors
  have hr := represents_of_context color _ source.focus source.ancestors ha extras rest hbefore hframes
  have he := Represents.unique color _ source h hr
  rw [he]
  obtain ⟨tail,ht⟩ := packed_root_head color source.focus ha
  refine ⟨extras,tail,?_⟩
  change (prepend extras actual).rootRecord = _
  cases actual <;> simpa only [prepend,Source.setRoot,Source.rootRecord] using congrArg (extras ++ ·) ht

theorem focus_bounded (capacity : Nat) (focus : Source α (List ρ))
    (rest : List (Frame α (List ρ)))
    (h : (plug focus rest).toStored.Bounded capacity) : focus.toStored.Bounded capacity := by
  induction rest generalizing focus with
  | nil => exact h
  | cons frame rest ih =>
    cases frame with
    | left record sibling => exact (ih (.fork record focus sibling) h).2.1
    | right sibling record => exact (ih (.fork record sibling focus) h).2.2

theorem represented_capacity [Fintype C] (color : α → C) (q : C) (source : Cursor α ρ)
    {physical : Cursor α (List ρ)} (h : Represents color q source physical) :
    physical.focus.rootRecord.length ≤ Fintype.card C := by
  have he := packed_toStored color q source.tree h.1
  have hb : physical.tree.toStored.Bounded (Fintype.card C) := by
    rw [he]; exact pack_bounded_colors color q source.tree
  have hf := (focus_bounded _ physical.focus physical.ancestors hb).root
  simpa only [Source.toStored_rootRecords] using hf

theorem read_record [Fintype C] (color : α → C) (source : Cursor α ρ)
    {physical : Cursor α (List ρ)}
    (h : Represents color (source.focus.rootOwner color) source physical) :
    SourcePointer.Trace physical [physical.focus.rootRecord] physical 1 ∧
      source.focus.rootRecord ∈ physical.focus.rootRecord ∧
      physical.focus.rootRecord.length ≤ Fintype.card C := by
  obtain ⟨extras,tail,he⟩ := record_at_cursor color source h
  exact ⟨.read (.nil _),by simp [he],represented_capacity color _ source h⟩

theorem Stored.toSource_replaceFirst (fresh : ρ) (t : Stored α ρ) :
    (t.replaceFirst fresh).toSource =
      t.toSource.map (fun a => a.setRoot (a.rootRecord.modifyHead (fun _ => fresh))) := by
  cases t with
  | empty => rfl
  | leaf => rfl
  | fork records l r =>
    cases hl : l.toSource <;> cases hr : r.toSource <;>
      simp [Stored.replaceFirst,Stored.toSource,hl,hr,Source.setRoot,Source.rootRecord]

theorem packed_setRoot (color : α → C) (q : C) (source : Source α ρ) (fresh : ρ) :
    packed color q (source.setRoot fresh) =
      if source.rootOwner color = q then
        (packed color q source).map
          (fun a => a.setRoot (a.rootRecord.modifyHead (fun _ => fresh)))
      else packed color q source := by
  by_cases hq : source.rootOwner color = q
  · simp [packed,pack_setRoot,hq,Stored.toSource_replaceFirst]
  · simp [packed,pack_setRoot,hq]

theorem write_record (color : α → C) (source : Cursor α ρ) (fresh : ρ)
    {physical : Cursor α (List ρ)}
    (h : Represents color (source.focus.rootOwner color) source physical) :
    ∃ actual : Cursor α (List ρ),
      SourcePointer.Trace physical [physical.focus.rootRecord] actual 2 ∧
      Represents color (source.focus.rootOwner color)
        ⟨source.focus.setRoot fresh,source.ancestors⟩ actual := by
  obtain ⟨a,ha⟩ := packed_exists color _ source.focus (Source.rootOwner_mem color _)
  let b := a.setRoot (a.rootRecord.modifyHead (fun _ => fresh))
  have hb : packed color (source.focus.rootOwner color) (source.focus.setRoot fresh) = some b := by
    simp only [packed_setRoot,if_true,ha,Option.map_some,b]
  obtain ⟨extras,rest,hbefore,hafter,hframes⟩ := packed_cursor_context color _
    (Source.support_setRoot color source.focus fresh).symm ha hb source.ancestors
  have hr := represents_of_context color _ source.focus source.ancestors ha extras rest hbefore hframes
  have he := Represents.unique color _ source h hr
  rw [he]
  refine ⟨⟨prepend extras b,rest⟩,?_,
    represents_of_context color _ _ _ hb extras rest hafter hframes⟩
  have hw := SourcePointer.write_charged (prepend extras a)
    (extras ++ a.rootRecord.modifyHead (fun _ => fresh)) rest
  have ht : (prepend extras a).setRoot
      (extras ++ a.rootRecord.modifyHead (fun _ => fresh)) = prepend extras b := by
    cases a <;> rfl
  simpa only [ht] using hw

theorem write_other (color : α → C) (q : C) (source : Cursor α ρ) (fresh : ρ)
    (hq : q ≠ source.focus.rootOwner color) {physical : Cursor α (List ρ)}
    (h : Represents color q source physical) :
    Represents color q ⟨source.focus.setRoot fresh,source.ancestors⟩ physical := by
  refine ⟨?_,?_⟩
  · have hp : packed color q (source.focus.setRoot fresh) = packed color q source.focus := by
      rw [packed_setRoot,if_neg (Ne.symm hq)]
    exact (packed_eq_context color q (Source.support_setRoot color _ _) hp _).trans h.1
  · simpa only [cursorShape,source_setRoot_shape] using h.2

end ChaCha.Paper20261030.ColoredStorage
