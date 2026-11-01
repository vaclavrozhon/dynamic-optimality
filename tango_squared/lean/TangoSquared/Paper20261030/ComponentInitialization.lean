import TangoSquared.Paper20261030.AuxiliaryComponents

/-!
# Initialization for arbitrary decorated references, including restrictions

The construction uses only existing child edges and the preferred-child
bit supplied by each record. It therefore also applies to completed and
pruned references while retaining their original split identities. No
reindexing of a restricted interval is required.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

def Source.internalCount {α ρ : Type*} : Source α ρ → Nat
  | .leaf _ _ => 0
  | .fork _ l r => l.internalCount + 1 + r.internalCount

end TangoSquared.Paper20261030.ColoredStorage

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata RouterProjection

variable {α κ : Type*} {β : κ → Type*}

def initializeSource (right : NodeRecord κ β → Bool) :
    Source α (NodeRecord κ β) → AuxiliaryComponent α κ β
  | .leaf key record => terminal (.leaf key record)
  | .fork record l r =>
      let left := initializeSource right l
      let next := initializeSource right r
      if right record then prepend record.2.1 record.2.2 left.tree next
      else append left record.2.1 record.2.2 next.tree

theorem initializeSource_size (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β)) :
    (initializeSource right source).core.size = (PathPorts.skeleton right source).size := by
  induction source with
  | leaf => rfl
  | fork record l r ihl ihr =>
    cases hp : right record <;>
      simp only [initializeSource,PathPorts.skeleton,hp,Bool.false_eq_true,if_false,if_true,
        prepend_size,append_size,MTR.Tree.size,ihl,ihr]
    all_goals omega

theorem skeleton_height (right : NodeRecord κ β → Bool) (source : Source α (NodeRecord κ β)) :
    (PathPorts.skeleton right source).size ≤ source.shape.height := by
  induction source with
  | leaf => exact le_rfl
  | fork record l r ihl ihr =>
    cases hp : right record <;>
      simp only [PathPorts.skeleton,hp,Bool.false_eq_true,if_false,if_true,
        MTR.Tree.size,Source.shape,Router.height] <;> omega

theorem initializeSource_word [Ord κ] (right : NodeRecord κ β → Bool)
    (source : Source α (NodeRecord κ β)) :
    (initializeSource right source).core.toListModel =
      (fromRecordTree (PathPorts.skeleton right source)).toListModel := by
  induction source with
  | leaf => rfl
  | fork record l r ihl ihr =>
    rcases record with ⟨cached,⟨key,value⟩⟩
    cases hp : right (cached,⟨key,value⟩) <;>
      simp only [initializeSource,PathPorts.skeleton,hp,Bool.false_eq_true,if_false,if_true,
        prepend_word,append_word,fromRecordTree,toListModel,ihl,ihr,List.nil_append,List.append_nil]

theorem initializeSource_charged (right : NodeRecord κ β → Bool)
    (source : Source α (NodeRecord κ β)) (K : Nat) (hheight : source.shape.height ≤ K) :
    SourcePointer.Rearranges source (initializeSource right source).tree
      ((495 * Nat.clog 2 (K + 1) + 81) * source.internalCount) := by
  induction source with
  | leaf key record => exact SourcePointer.rearranges_refl _ _
  | fork record l r ihl ihr =>
    rcases record with ⟨cached,⟨key,value⟩⟩
    have hl : l.shape.height ≤ K := by simp only [Source.shape,Router.height] at hheight; omega
    have hr : r.shape.height ≤ K := by simp only [Source.shape,Router.height] at hheight; omega
    have hleft := ihl hl
    have hright := ihr hr
    have read : SourcePointer.Rearranges (.fork (cached,⟨key,value⟩) l r)
        (.fork (cached,⟨key,value⟩) l r) 1 := fun rest => ⟨_,1,.read (.nil _),le_rfl⟩
    have prepared := (read.trans hleft.left).trans hright.right
    cases hp : right (cached,⟨key,value⟩)
    · have inserted := append_charged (initializeSource right l) key value
        (initializeSource right r).tree cached
      have full := prepared.trans inserted
      simp only [initializeSource,hp,Bool.false_eq_true,if_false]
      apply full.mono
      have hsize : (initializeSource right l).core.size ≤ K := by
        rw [initializeSource_size]; exact (skeleton_height right l).trans hl
      have hm := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
      simp only [Source.internalCount,Nat.mul_add,Nat.mul_one]
      omega
    · have inserted := prepend_charged key value (initializeSource right l).tree
        (initializeSource right r) cached
      have full := prepared.trans inserted
      simp only [initializeSource,hp,if_true]
      apply full.mono
      have hsize : (initializeSource right r).core.size ≤ K := by
        rw [initializeSource_size]; exact (skeleton_height right r).trans hr
      have hm := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
      simp only [Source.internalCount,Nat.mul_add,Nat.mul_one]
      omega

end TangoSquared.Paper20261030.AuxiliaryComponent
