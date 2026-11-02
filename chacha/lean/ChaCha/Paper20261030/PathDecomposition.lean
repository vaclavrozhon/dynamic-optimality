import ChaCha.Paper20261030.ComponentEquivalence
import ChaCha.Paper20261030.MarkedInitialization

/-!
# A maintained decomposition of a decorated reference into balanced paths

`Represents right reference component` connects an actual reference tree
to its physical root component. At a reference fork, the preferred child's
core is incorporated together with the fork record; the other child's
closed component occupies the new gap. Each core may use any balanced
shape with that exact record word and those exact ports (`Equivalent`).
Terminals and all component entrances are physically marked.

This invariant is inhabited by the charged initializer. It determines the
whole preferred-path word and bounds each root core by reference height;
it does not assume that a future access or head change preserves it.
-/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α κ : Type*} {β : κ → Type*}

inductive Represents (right : Record (β := β) → Bool) :
    Source α (Record (β := β)) → AuxiliaryComponent α κ (Tagged β) → Prop
  | leaf {key record c} (marked : entry record = true)
      (same : Equivalent c (terminal (.leaf key record))) :
      Represents right (.leaf key record) c
  | left {record l r lc rc c} (direction : right record = false) (clean : entry record = false)
      (left : Represents right l lc) (rightChild : Represents right r rc)
      (same : Equivalent c (append lc record.2.1 record.2.2 (closed rc))) :
      Represents right (.fork record l r) c
  | right {record l r lc rc c} (direction : right record = true) (clean : entry record = false)
      (leftChild : Represents right l lc) (rightChild : Represents right r rc)
      (same : Equivalent c (prepend record.2.1 record.2.2 (closed lc) rc)) :
      Represents right (.fork record l r) c

theorem Represents.equivalent {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c d : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) (same : Equivalent d c) : Represents right reference d := by
  cases h with
  | leaf marked he => exact .leaf marked (same.trans he)
  | left direction clean hl hr he => exact .left direction clean hl hr (same.trans he)
  | right direction clean hl hr he => exact .right direction clean hl hr (same.trans he)

theorem Represents.raw {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) : Raw reference := by
  induction h with
  | leaf marked => exact marked
  | left _ clean _ _ _ ihl ihr => exact ⟨clean,ihl,ihr⟩
  | right _ clean _ _ _ ihl ihr => exact ⟨clean,ihl,ihr⟩

theorem Represents.left_view {right : Record (β := β) → Bool} {record : Record (β := β)}
    {l r : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right (.fork record l r) c) (direction : right record = false) :
    ∃ lc rc, Represents right l lc ∧ Represents right r rc ∧
      Equivalent c (append lc record.2.1 record.2.2 (closed rc)) := by
  cases h with
  | left _ _ hl hr same => exact ⟨_,_,hl,hr,same⟩
  | right hd => simp [direction] at hd

theorem Represents.right_view {right : Record (β := β) → Bool} {record : Record (β := β)}
    {l r : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right (.fork record l r) c) (direction : right record = true) :
    ∃ lc rc, Represents right l lc ∧ Represents right r rc ∧
      Equivalent c (prepend record.2.1 record.2.2 (closed lc) rc) := by
  cases h with
  | left hd => simp [direction] at hd
  | right _ _ hl hr same => exact ⟨_,_,hl,hr,same⟩

theorem Represents.invariant [Ord κ] {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) : Clean c.core ∧ MarkedPorts c := by
  induction h with
  | leaf marked same =>
    exact ⟨same.clean True.intro,same.marked (fun _ _ => marked)⟩
  | @left record l r lc rc c direction clean hl hr same ihl ihr =>
    have hc := clean_append lc ihl.1 record.2.1 record.2.2 clean (closed rc)
    have hp := marked_append lc ihl.2 record.2.1 record.2.2 (closed rc) (closed_entry rc)
    exact ⟨same.clean hc,same.marked hp⟩
  | @right record l r lc rc c direction clean hl hr same ihl ihr =>
    have hc := clean_prepend record.2.1 record.2.2 clean (closed lc) rc ihr.1
    have hp := marked_prepend record.2.1 record.2.2 (closed lc) (closed_entry lc) rc ihr.2
    exact ⟨same.clean hc,same.marked hp⟩

theorem Represents.word [Ord κ] {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) :
    c.core.toListModel = (fromRecordTree (PathPorts.skeleton right reference)).toListModel := by
  induction h with
  | leaf marked same => exact same.word
  | @left record l r lc rc c direction clean hl hr same ihl ihr =>
    rw [same.word,append_word,ihl]
    simp only [PathPorts.skeleton,direction,Bool.false_eq_true,if_false,fromRecordTree,
      toListModel_inner,toListModel_leaf]
  | @right record l r lc rc c direction clean hl hr same ihl ihr =>
    rw [same.word,prepend_word,ihr]
    simp only [PathPorts.skeleton,direction,if_true,fromRecordTree,
      toListModel_inner,toListModel_leaf,List.nil_append]

theorem Represents.size [Ord κ] {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) : c.core.size = (PathPorts.skeleton right reference).size := by
  rw [size_eq_length c.core c.balanced,h.word,← actualSize_length,actualSize_fromRecordTree]

theorem Represents.size_height [Ord κ] {right : Record (β := β) → Bool}
    {reference : Source α (Record (β := β))} {c : AuxiliaryComponent α κ (Tagged β)}
    (h : Represents right reference c) : c.core.size ≤ reference.shape.height := by
  rw [h.size]
  exact skeleton_height right reference

theorem initialize_represents [Ord κ] (right : Record (β := β) → Bool)
    (reference : Source α (Record (β := β))) (raw : Raw reference) :
    Represents right reference (initializeMarked right reference) := by
  induction reference with
  | leaf key record => exact .leaf raw (.refl _)
  | fork record l r ihl ihr =>
    have hl := ihl raw.2.1
    have hr := ihr raw.2.2
    cases hd : right record
    · simp only [initializeMarked,hd,Bool.false_eq_true,if_false]
      exact .left hd raw.1 hl hr (.refl _)
    · simp only [initializeMarked,hd,if_true]
      exact .right hd raw.1 hl hr (.refl _)

end ChaCha.Paper20261030.PathDecomposition
