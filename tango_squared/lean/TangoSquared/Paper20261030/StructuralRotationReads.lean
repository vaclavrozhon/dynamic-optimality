import TangoSquared.Paper20261030.SourceStructuralFields
import TangoSquared.Paper20261030.SecondaryRecordIds

/-!
# Computing rotation metadata from the records actually read

The two pivot records contain every child identifier and color mask needed
to construct their post-rotation fields. The middle subtree's root changes
only its parent field. A charged observation tour reads both pivots and
returns to the initial cursor before the existing rotation kernel runs.
-/

namespace TangoSquared.Paper20261030.Structural

open ColoredStorage SourcePointer

variable {α ρ ι C : Type*} [DecidableEq C]

def reparent (parent : Option ι) (record : ρ × Fields ι C) : ρ × Fields ι C :=
  (record.1,{record.2 with parent := parent})

theorem reparent_root (identifier : ρ → ι) (color : α → C) (old fresh : Option ι) (source : Source α ρ) :
    reparent fresh (annotate identifier color old source).rootRecord =
      (annotate identifier color fresh source).rootRecord := by
  rw [annotate_root,annotate_root]
  rfl

def rightPivotRecords (identifier : ρ → ι) (oldQ oldP : ρ × Fields ι C) :
    Option ((ρ × Fields ι C) × (ρ × Fields ι C)) :=
  match oldQ.2.children,oldP.2.children with
  | some (_,w),some (u,v) =>
      let newQ := (oldQ.1,Fields.mk (some (identifier oldP.1)) (v.colors ∪ w.colors) (some (v,w)))
      let newP := (oldP.1,Fields.mk oldQ.2.parent oldQ.2.colors
        (some (u,Child.mk (identifier oldQ.1) newQ.2.colors)))
      some (newP,newQ)
  | _,_ => none

theorem rightPivotRecords_exact (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) :
    rightPivotRecords identifier
      (annotate identifier color parent (.fork q (.fork p u v) w)).rootRecord
      (annotate identifier color (some (identifier q)) (.fork p u v)).rootRecord =
      some ((annotate identifier color parent (.fork p u (.fork q v w))).rootRecord,
        (annotate identifier color (some (identifier p)) (.fork q v w)).rootRecord) := by
  simp only [annotate,Source.rootRecord,rightPivotRecords,fields,descriptor,Source.support,Finset.union_assoc]

theorem right_pivot_tour (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) (outside : List (Frame α (ρ × Fields ι C))) :
    Trace ⟨annotate identifier color parent (.fork q (.fork p u v) w),outside⟩
      [(annotate identifier color parent (.fork q (.fork p u v) w)).rootRecord,
       (annotate identifier color (some (identifier q)) (.fork p u v)).rootRecord]
      ⟨annotate identifier color parent (.fork q (.fork p u v) w),outside⟩ 4 :=
  .read (.step (.left _ _ _ _) (.read (.step (.upLeft _ _ _ _) (.nil _))))

theorem observed_rotate_right (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) (outside : List (Frame α (ρ × Fields ι C))) :
    ∃ observations cost,
      Trace ⟨annotate identifier color parent (.fork q (.fork p u v) w),outside⟩
        ([(annotate identifier color parent (.fork q (.fork p u v) w)).rootRecord,
          (annotate identifier color (some (identifier q)) (.fork p u v)).rootRecord] ++ observations)
        ⟨annotate identifier color parent (.fork p u (.fork q v w)),outside⟩ cost ∧ cost ≤ 17 := by
  obtain ⟨reads,cost,trace,bounded⟩ := rotate_right identifier color parent u v w p q outside
  exact ⟨reads,4+cost,(right_pivot_tour identifier color parent u v w p q outside).append trace,by omega⟩

theorem annotate_distinguishes (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (source : Source α ρ) (unique : (source.inventory identifier).Nodup) :
    Distinguishes (fun record => identifier record.1) (annotate identifier color parent source) := by
  apply Multiset.inj_on_of_nodup_map
  change ((annotate identifier color parent source).inventory (fun record => identifier record.1)).Nodup
  rw [annotate_inventory]
  exact unique

end TangoSquared.Paper20261030.Structural
