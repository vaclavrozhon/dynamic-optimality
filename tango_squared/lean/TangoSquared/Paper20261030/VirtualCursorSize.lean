import TangoSquared.Paper20261030.VirtualStorage
import TangoSquared.Paper20261030.PackedRecordAccess
import TangoSquared.Paper20261030.SourcePayloadCapacity

/-!
# A virtual projection and its current cursor fit in a constant-size header

With at most two virtual leaves, the projection is empty, one leaf, or a
fork of two leaves. Its cursor has at most one ancestor frame. A three-color
packing stores at most nine source records in this entire projection.
Keeping this bounded cursor value in a physical header therefore retains
its shape, leaf labels, records, and cursor position; flattening only the
record list would not retain all of that information.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

open SourcePointer RouterProjection

variable {α ρ : Type*}

theorem Source.leaf_count_pos (source : Source α ρ) : 0 < source.shape.leaves.length := by
  induction source <;> simp_all [Source.shape,Router.leaves] <;> omega

theorem Source.one_leaf (source : Source α ρ) (bound : source.shape.leaves.length ≤ 1) :
    ∃ key record, source = .leaf key record := by
  cases source with
  | leaf key record => exact ⟨key,record,rfl⟩
  | fork record l r =>
    have hl := l.leaf_count_pos
    have hr := r.leaf_count_pos
    simp only [Source.shape,Router.leaves,List.length_append] at bound
    omega

theorem Source.two_leaves (source : Source α ρ) (bound : source.shape.leaves.length ≤ 2) :
    (∃ key record, source = .leaf key record) ∨
      ∃ record leftKey leftRecord rightKey rightRecord,
        source = .fork record (.leaf leftKey leftRecord) (.leaf rightKey rightRecord) := by
  cases source with
  | leaf key record => exact Or.inl ⟨key,record,rfl⟩
  | fork record l r =>
    have hl := l.leaf_count_pos
    have hr := r.leaf_count_pos
    simp only [Source.shape,Router.leaves,List.length_append] at bound
    obtain ⟨lk,lr,rfl⟩ := l.one_leaf (by omega)
    obtain ⟨rk,rr,rfl⟩ := r.one_leaf (by omega)
    exact Or.inr ⟨record,lk,lr,rk,rr,rfl⟩

theorem cursor_depth_leaf_count (focus : Source α ρ) (ancestors : List (Frame α ρ)) :
    ancestors.length + focus.shape.leaves.length ≤ (plug focus ancestors).shape.leaves.length := by
  induction ancestors generalizing focus with
  | nil => simpa only [List.length_nil,Nat.zero_add,plug] using Nat.le_refl focus.shape.leaves.length
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      have parent := ih (.fork record focus sibling)
      have positive := sibling.leaf_count_pos
      simp only [Source.shape,Router.leaves,List.length_append] at parent
      simp only [List.length_cons,plug]
      omega
    | right sibling record =>
      have parent := ih (.fork record sibling focus)
      have positive := sibling.leaf_count_pos
      simp only [Source.shape,Router.leaves,List.length_append] at parent
      simp only [List.length_cons,plug]
      omega

theorem virtual_cursor_depth (cursor : Cursor α ρ) (bound : cursor.tree.shape.leaves.length ≤ 2) :
    cursor.ancestors.length ≤ 1 := by
  have depth := cursor_depth_leaf_count cursor.focus cursor.ancestors
  have positive := cursor.focus.leaf_count_pos
  change (plug cursor.focus cursor.ancestors).shape.leaves.length ≤ 2 at bound
  omega

theorem virtual_records_bound (source : Source α (List ρ)) (leaves : source.shape.leaves.length ≤ 2)
    (capacity : source.Bounded 3) : source.toStored.recordList.length ≤ 9 := by
  rcases source.two_leaves leaves with ⟨key,record,rfl⟩ | ⟨record,lk,lr,rk,rr,rfl⟩
  · exact capacity.trans (by decide)
  · change record.length ≤ 3 ∧ lr.length ≤ 3 ∧ rr.length ≤ 3 at capacity
    simp only [Source.toStored,Stored.recordList,List.length_append]
    omega

structure VirtualCursor (α ρ : Type*) where
  actual : Option (Cursor α (List ρ))
  small : ∀ cursor, actual = some cursor → cursor.tree.shape.leaves.length ≤ 2
  bounded : ∀ cursor, actual = some cursor → cursor.tree.Bounded 3

theorem VirtualCursor.depth (header : VirtualCursor α ρ) (cursor : Cursor α (List ρ))
    (present : header.actual = some cursor) : cursor.ancestors.length ≤ 1 :=
  virtual_cursor_depth cursor (header.small cursor present)

theorem VirtualCursor.records (header : VirtualCursor α ρ) (cursor : Cursor α (List ρ))
    (present : header.actual = some cursor) : cursor.tree.toStored.recordList.length ≤ 9 :=
  virtual_records_bound cursor.tree (header.small cursor present) (header.bounded cursor present)

theorem header_update (key : α) (before after : VirtualCursor α ρ) (outside : List (Frame α (VirtualCursor α ρ))) :
    Trace ⟨Source.leaf key before,outside⟩ [before] ⟨Source.leaf key after,outside⟩ 2 :=
  write_charged _ _ _

end TangoSquared.Paper20261030.ColoredStorage
