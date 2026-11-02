import ChaCha.Paper20261030.SourcePointer

/-!
# Physical record lists at projected vertices

A nonempty packed color projection is represented by the existing
leaf-oriented source tree, with a list of stored records at each vertex.
The earlier packing theorem bounds each list by the number of colors.
This module checks the representation and compiles a root-slot update
into an actual read and write at the corresponding physical vertex.
-/

namespace ChaCha.Paper20261030.ColoredStorage

variable {α ρ C : Type*}

def Source.toStored : Source α (List ρ) → Stored α ρ
  | .leaf key records => .leaf key records
  | .fork records l r => .fork records l.toStored r.toStored

def Stored.toSource : Stored α ρ → Option (Source α (List ρ))
  | .empty => none
  | .leaf key records => some (.leaf key records)
  | .fork records l r =>
    match l.toSource,r.toSource with
    | some left,some right => some (.fork records left right)
    | _,_ => none

def storedOption : Option (Source α (List ρ)) → Stored α ρ
  | none => .empty
  | some t => t.toStored

theorem Source.toStored_shape (t : Source α (List ρ)) : t.toStored.shape = t.shape := by
  induction t <;> simp_all [Source.toStored,Stored.shape,Source.shape]

theorem Source.toStored_rootRecords (t : Source α (List ρ)) : t.toStored.rootRecords = t.rootRecord := by
  cases t <;> rfl

theorem Stored.toSource_roundtrip (t : Stored α ρ) (hf : Router.Full t.shape) :
    storedOption t.toSource = t := by
  induction t with
  | empty => rfl
  | leaf => rfl
  | fork records l r ihl ihr =>
    obtain ⟨hl,hr,hfl,hfr⟩ := hf
    have il := ihl hfl
    have ir := ihr hfr
    cases hls : l.toSource with
    | none =>
      have he : l = .empty := by simpa only [hls,storedOption] using il.symm
      simp [he,Stored.shape] at hl
    | some left =>
      cases hrs : r.toSource with
      | none =>
        have he : r = .empty := by simpa only [hrs,storedOption] using ir.symm
        simp [he,Stored.shape] at hr
      | some right =>
        simpa only [Stored.toSource,hls,hrs,storedOption,Source.toStored] using
          congrArg₂ (Stored.fork records) il ir

theorem Stored.toSource_exists (t : Stored α ρ) (hf : Router.Full t.shape) (hne : t ≠ .empty) :
    ∃ actual, t.toSource = some actual ∧ actual.toStored = t := by
  have hi := t.toSource_roundtrip hf
  cases ht : t.toSource with
  | none => exact False.elim (hne (by simpa only [ht,storedOption] using hi.symm))
  | some actual => exact ⟨actual,rfl,by simpa only [ht,storedOption] using hi⟩

theorem pack_physical [LinearOrder C] [Fintype C] (color : α → C) (q : C) (t : Source α ρ)
    (hq : q ∈ t.support color) :
    ∃ actual : Source α (List ρ), (pack color q t).toSource = some actual ∧
      actual.toStored = pack color q t ∧ actual.toStored.Bounded (Fintype.card C) := by
  have hf : Router.Full (pack color q t).shape := by
    rw [pack_shape]
    exact Router.full_prune _ _
  obtain ⟨actual,he,hi⟩ := Stored.toSource_exists _ hf ((pack_nonempty color q t).mpr hq)
  exact ⟨actual,he,hi,by rw [hi]; exact pack_bounded_colors color q t⟩

theorem RootWrite.physical {before after : Stored α ρ} (h : RootWrite before after)
    {actual final : Source α (List ρ)} (hb : before.toSource = some actual)
    (ha : after.toSource = some final) (ancestors) :
    SourcePointer.Trace ⟨actual,ancestors⟩ [actual.rootRecord] ⟨final,ancestors⟩ 2 := by
  cases h with
  | leaf key old fresh tail =>
    have he : actual = .leaf key (old :: tail) := (Option.some.inj hb).symm
    have hf : final = .leaf key (fresh :: tail) := (Option.some.inj ha).symm
    subst actual
    subst final
    exact SourcePointer.write_charged _ _ _
  | fork old fresh tail l r =>
    cases hl : l.toSource with
    | none => simp [Stored.toSource,hl] at hb
    | some left =>
      cases hr : r.toSource with
      | none => simp [Stored.toSource,hl,hr] at hb
      | some right =>
        have he : actual = .fork (old :: tail) left right := by
          simpa only [Stored.toSource,hl,hr,Option.some.injEq] using hb.symm
        have hf : final = .fork (fresh :: tail) left right := by
          simpa only [Stored.toSource,hl,hr,Option.some.injEq] using ha.symm
        subst actual
        subst final
        exact SourcePointer.write_charged _ _ _

end ChaCha.Paper20261030.ColoredStorage
