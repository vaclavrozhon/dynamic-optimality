import TangoSquared.Paper20261030.GapBSTStorage

/-! Charged compilation of every source instruction into the appendix's
ordinary-BST record layout. Rotations explicitly read both pivots and
transfer the middle leaf's slot between them. Source observations occur
in order among the locally read physical records. -/

namespace TangoSquared.Paper20261030.GapBST.Storage

open ColoredStorage
open Auxiliary.Metadata (Trace Step)

variable {α ρ : Type*}

theorem step_trace {before after : SourcePointer.Cursor α ρ} (move : SourcePointer.Step before after) :
    ∃ reads cost, Trace (cursor before) reads (cursor after) cost ∧ cost ≤ 7 := by
  cases move with
  | left left right value rest =>
    cases left with
    | leaf key old => exact ⟨[],0,.nil _,by decide⟩
    | fork old a b => exact ⟨[],1,.step (.nav (.left _ _ _ _ _ _)) (.nil _),by decide⟩
  | right left right value rest =>
    cases right with
    | leaf key old => exact ⟨[],0,.nil _,by decide⟩
    | fork old a b => exact ⟨[],1,.step (.nav (.right _ _ _ _ _ _)) (.nil _),by decide⟩
  | upLeft left right value rest =>
    cases left with
    | leaf key old => exact ⟨[],0,.nil _,by decide⟩
    | fork old a b => exact ⟨[],1,.step (.nav (.upLeft _ _ _ _)) (.nil _),by decide⟩
  | upRight left right value rest =>
    cases right with
    | leaf key old => exact ⟨[],0,.nil _,by decide⟩
    | fork old a b => exact ⟨[],1,.step (.nav (.upRight _ _ _ _)) (.nil _),by decide⟩
  | rotateRight u v w p q rest =>
    refine ⟨[record (lastKey v) ⟨some q,none,leafRecord w⟩,
      record (lastKey u) ⟨some p,leafRecord u,leafRecord v⟩],7,?_,le_rfl⟩
    exact .read rfl (.step (.nav (.left _ _ _ _ _ _)) (.read rfl
      (.step (.writeValue _ _ 0 (lastKey u) _ ⟨some p,leafRecord u,none⟩ _)
      (.step (.nav (.upLeft _ _ _ _))
      (.step (.writeValue _ _ 0 (lastKey v) _ ⟨some q,leafRecord v,leafRecord w⟩ _)
      (.step (.nav (.rotateRight _ _ _ _ _ _)) (.nil _)))))))
  | rotateLeft u v w p q rest =>
    refine ⟨[record (lastKey u) ⟨some p,leafRecord u,none⟩,
      record (lastKey v) ⟨some q,leafRecord v,leafRecord w⟩],7,?_,le_rfl⟩
    exact .read rfl (.step (.nav (.right _ _ _ _ _ _)) (.read rfl
      (.step (.writeValue _ _ 0 (lastKey v) _ ⟨some q,none,leafRecord w⟩ _)
      (.step (.nav (.upRight _ _ _ _))
      (.step (.writeValue _ _ 0 (lastKey u) _ ⟨some p,leafRecord u,leafRecord v⟩ _)
      (.step (.nav (.rotateLeft _ _ _ _ _ _)) (.nil _)))))))
  | write focus fresh rest =>
    refine ⟨[],1,?_,by decide⟩
    cases focus with
    | fork old left right => exact .step (.writeValue _ _ _ _ _ _ _) (.nil _)
    | leaf key old =>
      cases rest with
      | nil => exact .step (.writeValue _ _ _ _ _ _ _) (.nil _)
      | cons first rest => cases first <;> exact .step (.writeValue _ _ _ _ _ _ _) (.nil _)

def observations (reads : List (Auxiliary.NodeRecord α (fun _ => Slots ρ))) : List ρ :=
  reads.flatMap (fun entry => entry.2.2.values)

/-- The physical reads contain every requested source observation in its
original order. Extra reads are the charged pivot observations. -/
theorem trace {before after : SourcePointer.Cursor α ρ} {reads : List ρ} {budget : Nat}
    (run : SourcePointer.Trace before reads after budget) :
    ∃ physicalReads cost, Trace (cursor before) physicalReads (cursor after) cost ∧
      reads.Sublist (observations physicalReads) ∧ cost ≤ 7*budget := by
  induction run with
  | nil => exact ⟨[],0,.nil _,List.Sublist.refl [],by omega⟩
  | step move rest ih =>
    obtain ⟨firstReads,firstCost,first,firstBound⟩ := step_trace move
    obtain ⟨lastReads,lastCost,last,included,lastBound⟩ := ih
    refine ⟨firstReads++lastReads,firstCost+lastCost,first.append last,?_,by omega⟩
    simpa only [observations,List.flatMap_append] using
      included.trans (List.sublist_append_right (observations firstReads) (observations lastReads))
  | @read current last reads budget rest ih =>
    obtain ⟨physicalReads,cost,physical,included,bound⟩ := ih
    obtain ⟨entry,atRecord,contains⟩ := cursor_record current
    refine ⟨entry::physicalReads,cost+1,.read atRecord physical,?_,by omega⟩
    have singleton : [current.focus.rootRecord].Sublist entry.2.2.values :=
      List.singleton_sublist.mpr (readSlot_mem contains)
    simpa only [observations,List.flatMap_cons,List.singleton_append] using singleton.append included

end TangoSquared.Paper20261030.GapBST.Storage
