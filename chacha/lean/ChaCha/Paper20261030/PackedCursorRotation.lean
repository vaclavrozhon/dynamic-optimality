import ChaCha.Paper20261030.PackedRecordAccess
import ChaCha.Paper20261030.SourceReversal

/-!
# Rotating at the maintained physical color cursor

For every color present in the whole component, a source rotation is
implemented at that color's current active or parked cursor. The complete
packed record tree and the cursor representation are preserved. The
local record-list kernel requires the pivot values to have been read;
this theorem does not yet supply structural fields or simultaneous
positions for other source cursors.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer ProjectionLocal RouterProjection

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem packed_none_iff (color : α → C) (q : C) (source : Source α ρ) :
    packed color q source = none ↔ q ∉ source.support color := by
  constructor
  · intro hn hq
    obtain ⟨actual,he⟩ := packed_exists color q source hq
    rw [hn] at he
    contradiction
  · intro hq
    have he : pack color q source = .empty := by
      by_contra hn
      exact hq ((pack_nonempty color q source).mp hn)
    simp only [packed,he,Stored.toSource]

theorem rearrange_at_cursor (color : α → C) (q : C)
    (s t : Source α ρ) (ancestors : List (Frame α ρ)) (budget : Nat)
    (hs : s.support color = t.support color)
    (kernel : ∀ extras : List ρ,
      ProjectionLocal.Rearranges
        (ProjectionLocal.decorate extras (packed color q s))
        (ProjectionLocal.decorate extras (packed color q t)) budget)
    {physical : Cursor α (List ρ)} (h : Represents color q ⟨s,ancestors⟩ physical) :
    ∃ (actual : Cursor α (List ρ)) (reads : List (List ρ)) (cost : Nat),
      SourcePointer.Trace physical reads actual cost ∧ cost ≤ budget ∧
      Represents color q ⟨t,ancestors⟩ actual := by
  cases ha : packed color q s with
  | none =>
    have hb : packed color q t = none :=
      (packed_none_iff color q t).mpr (hs ▸ (packed_none_iff color q s).mp ha)
    have hsa := packed_none_shape color q s ha
    have htb := packed_none_shape color q t hb
    refine ⟨physical,[],0,.nil _,Nat.zero_le _,?_,?_⟩
    · exact (packed_eq_context color q hs.symm (hb.trans ha.symm) ancestors).trans h.1
    · simpa only [LeafPointer.project,cursorShape,hsa,htb,if_true] using h.2
  | some a =>
    have hq : q ∈ s.support color := by
      by_contra hn
      have he := (packed_none_iff color q s).mpr hn
      rw [ha] at he
      contradiction
    obtain ⟨b,hb⟩ := packed_exists color q t (hs ▸ hq)
    obtain ⟨extras,rest,hbefore,hafter,hframes⟩ := packed_cursor_context color q hs ha hb ancestors
    have before := represents_of_context color q s ancestors ha extras rest hbefore hframes
    have after := represents_of_context color q t ancestors hb extras rest hafter hframes
    have he := Represents.unique color q _ h before
    have ht := kernel extras
    rw [ha,hb] at ht
    obtain ⟨reads,cost,trace,hcost⟩ := ht rest
    exact ⟨⟨prepend extras b,rest⟩,reads,cost,he.symm ▸ trace,hcost,after⟩

theorem rotate_right (color : α → C) (q : C)
    (u v w : Source α ρ) (p r : ρ) (ancestors : List (Frame α ρ))
    {physical : Cursor α (List ρ)}
    (h : Represents color q ⟨.fork r (.fork p u v) w,ancestors⟩ physical) :
    ∃ (actual : Cursor α (List ρ)) (reads : List (List ρ)) (cost : Nat),
      SourcePointer.Trace physical reads actual cost ∧ cost ≤ 17 ∧
      Represents color q ⟨.fork p u (.fork r v w),ancestors⟩ actual := by
  exact rearrange_at_cursor color q _ _ ancestors 17
    (by simp only [Source.support,Finset.union_assoc])
    (packed_rotation_decorated color q u v w p r) h

theorem rotate_left (color : α → C) (q : C)
    (u v w : Source α ρ) (p r : ρ) (ancestors : List (Frame α ρ))
    {physical : Cursor α (List ρ)}
    (h : Represents color q ⟨.fork p u (.fork r v w),ancestors⟩ physical) :
    ∃ (actual : Cursor α (List ρ)) (reads : List (List ρ)) (cost : Nat),
      SourcePointer.Trace physical reads actual cost ∧ cost ≤ 17 ∧
      Represents color q ⟨.fork r (.fork p u v) w,ancestors⟩ actual := by
  exact rearrange_at_cursor color q _ _ ancestors 17
    (by simp only [Source.support,Finset.union_assoc])
    (fun extras => (packed_rotation_decorated color q u v w p r extras).symm) h

end ChaCha.Paper20261030.ColoredStorage
