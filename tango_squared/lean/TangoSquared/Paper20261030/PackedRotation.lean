import TangoSquared.Paper20261030.ProjectionRecords
import TangoSquared.Paper20261030.ProjectionLocal

/-!
# Actual packed records after a source-root rotation

The checked local update is applied to the actual colored packing. For
each color it transforms the old physical record lists into the new
packing, including pivot records whose owning color changes. The two
pivot values must be available before the transformation, as required by
the local kernel. Ancestor records stored at the changed projected root,
and simultaneous cursors, are not yet included in this theorem.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

variable {α ρ C : Type*}

theorem Source.toStored_toSource (t : Source α (List ρ)) : t.toStored.toSource = some t := by
  induction t <;> simp_all [Source.toStored,Stored.toSource]

theorem storedOption_toSource (t : Option (Source α (List ρ))) : (storedOption t).toSource = t := by
  cases t
  · rfl
  · exact Source.toStored_toSource _

theorem storedOption_join (l r : ProjectionLocal.Projected α ρ) :
    storedOption (ProjectionLocal.join l r) = (storedOption l).join (storedOption r) := by
  cases l with
  | none => rfl
  | some l =>
    cases r with
    | none => simp [ProjectionLocal.join,storedOption,Stored.join_empty_right]
    | some r => cases l <;> cases r <;> rfl

theorem Stored.toSource_join {l r : Stored α ρ} (hl : Router.Full l.shape) (hr : Router.Full r.shape) :
    (l.join r).toSource = ProjectionLocal.join l.toSource r.toSource := by
  have he := storedOption_join l.toSource r.toSource
  rw [l.toSource_roundtrip hl,r.toSource_roundtrip hr] at he
  rw [← he,storedOption_toSource]

theorem Stored.toSource_addRoot (record : ρ) (t : Stored α ρ) :
    (t.addRoot record).toSource =
      t.toSource.map (fun s => s.setRoot (record :: s.rootRecord)) := by
  cases t with
  | empty => rfl
  | leaf => rfl
  | fork records l r =>
    cases hl : l.toSource <;> cases hr : r.toSource <;>
      simp [Stored.addRoot,Stored.toSource,hl,hr,Source.setRoot,Source.rootRecord]

def packed [LinearOrder C] (color : α → C) (q : C) (t : Source α ρ) : ProjectionLocal.Projected α ρ :=
  (pack color q t).toSource

theorem packed_fork [LinearOrder C] (color : α → C) (q : C) (record : ρ) (l r : Source α ρ) :
    packed color q (.fork record l r) =
      ProjectionLocal.attach (decide (owner color l r = q)) record
        (ProjectionLocal.join (packed color q l) (packed color q r)) := by
  have hl : Router.Full (pack color q l).shape := by rw [pack_shape]; exact Router.full_prune _ _
  have hr : Router.Full (pack color q r).shape := by rw [pack_shape]; exact Router.full_prune _ _
  by_cases ho : owner color l r = q
  · simp [packed,pack,Stored.toSource_addRoot,Stored.toSource_join hl hr,ProjectionLocal.attach,ho]
  · simp [packed,pack,Stored.toSource_join hl hr,ProjectionLocal.attach,ho]

theorem packed_rotation [LinearOrder C] (color : α → C) (q : C)
    (u v w : Source α ρ) (p r : ρ) :
    ProjectionLocal.Rearranges
      (packed color q (.fork r (.fork p u v) w))
      (packed color q (.fork p u (.fork r v w))) 13 := by
  simp only [packed_fork]
  exact ProjectionLocal.local_rotation _ _ _ _ _ _ _ _ _

theorem packed_rotation_decorated [LinearOrder C] (color : α → C) (q : C)
    (u v w : Source α ρ) (p r : ρ) (extras : List ρ) :
    ProjectionLocal.Rearranges
      (ProjectionLocal.decorate extras (packed color q (.fork r (.fork p u v) w)))
      (ProjectionLocal.decorate extras (packed color q (.fork p u (.fork r v w)))) 17 := by
  simp only [packed_fork]
  exact ProjectionLocal.local_rotation_decorated _ _ _ _ _ _ _ _ _ _

end TangoSquared.Paper20261030.ColoredStorage
