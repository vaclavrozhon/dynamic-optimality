import TangoSquared.Paper20261030.MarkedInsertion
import TangoSquared.Paper20261030.ComponentInitialization

/-!
# Initializing the physical component-entry invariant

The raw reference marks terminals and leaves its internal records
unmarked. Recursive initialization returns closed, balanced components.
Their cores remain clean and every hanging port root is marked. The
construction retains all original application fields and reference
identities, including those of a restricted reference.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent RouterProjection

variable {α κ : Type*} {β : κ → Type*} [Ord κ]

def Raw : Source α (Record (β := β)) → Prop
  | .leaf _ record => entry record = true
  | .fork record l r => entry record = false ∧ Raw l ∧ Raw r

def initializeMarked (right : Record (β := β) → Bool) :
    Source α (Record (β := β)) → AuxiliaryComponent α κ (Tagged β)
  | .leaf key record => terminal (.leaf key record)
  | .fork record l r =>
      let left := initializeMarked right l
      let next := initializeMarked right r
      if right record then prepend record.2.1 record.2.2 (closed left) next
      else append left record.2.1 record.2.2 (closed next)

theorem initialized_invariant (right : Record (β := β) → Bool) (source : Source α (Record (β := β)))
    (raw : Raw source) :
    Clean (initializeMarked right source).core ∧ MarkedPorts (initializeMarked right source) := by
  induction source with
  | leaf key record => exact ⟨True.intro,fun _ _ => raw⟩
  | fork record l r ihl ihr =>
    obtain ⟨hl,hpl⟩ := ihl raw.2.1
    obtain ⟨hr,hpr⟩ := ihr raw.2.2
    have hv : record.2.2.2 = false := raw.1
    cases hp : right record
    · simp only [initializeMarked,hp,Bool.false_eq_true,if_false]
      exact ⟨clean_append _ hl _ _ hv _,marked_append _ hpl _ _ _ (closed_entry _)⟩
    · simp only [initializeMarked,hp,if_true]
      exact ⟨clean_prepend _ _ hv _ _ hr,marked_prepend _ _ _ (closed_entry _) _ hpr⟩

theorem initializeMarked_size (right : Record (β := β) → Bool) (source : Source α (Record (β := β))) :
    (initializeMarked right source).core.size = (PathPorts.skeleton right source).size := by
  induction source with
  | leaf => rfl
  | fork record l r ihl ihr =>
    cases hp : right record <;>
      simp only [initializeMarked,PathPorts.skeleton,hp,Bool.false_eq_true,if_false,if_true,
        prepend_size,append_size,MTR.Tree.size,ihl,ihr]
    all_goals omega

theorem initializeMarked_word (right : Record (β := β) → Bool) (source : Source α (Record (β := β))) :
    (initializeMarked right source).core.toListModel =
      (fromRecordTree (PathPorts.skeleton right source)).toListModel := by
  induction source with
  | leaf => rfl
  | fork record l r ihl ihr =>
    rcases record with ⟨cached,⟨key,value⟩⟩
    cases hp : right (cached,⟨key,value⟩) <;>
      simp only [initializeMarked,PathPorts.skeleton,hp,Bool.false_eq_true,if_false,if_true,
        prepend_word,append_word,fromRecordTree,toListModel,ihl,ihr,List.nil_append,List.append_nil]

theorem initializeMarked_charged (right : Record (β := β) → Bool)
    (source : Source α (Record (β := β))) (raw : Raw source)
    (K : Nat) (hheight : source.shape.height ≤ K) :
    SourcePointer.Rearranges source (closed (initializeMarked right source))
      ((495 * Nat.clog 2 (K + 1) + 87) * source.internalCount) := by
  induction source with
  | leaf key record =>
    have he : closed (terminal (Source.leaf key record)) = Source.leaf key record :=
      closed_terminal _ rfl (fun _ _ => raw)
    rw [show initializeMarked right (.leaf key record) = terminal (.leaf key record) from rfl,he]
    exact SourcePointer.rearranges_refl _ _
  | fork record l r ihl ihr =>
    rcases record with ⟨cached,⟨key,value⟩⟩
    have hl : l.shape.height ≤ K := by simp only [Source.shape,Router.height] at hheight; omega
    have hr : r.shape.height ≤ K := by simp only [Source.shape,Router.height] at hheight; omega
    have hleft := ihl raw.2.1 hl
    have hright := ihr raw.2.2 hr
    obtain ⟨hcl,hpl⟩ := initialized_invariant right l raw.2.1
    obtain ⟨hcr,hpr⟩ := initialized_invariant right r raw.2.2
    have read : SourcePointer.Rearranges (.fork (cached,⟨key,value⟩) l r)
        (.fork (cached,⟨key,value⟩) l r) 1 := fun rest => ⟨_,1,.read (.nil _),le_rfl⟩
    have prepared := (read.trans hleft.left).trans hright.right
    cases hp : right (cached,⟨key,value⟩)
    · have inserted := appendMarked_charged (initializeMarked right l) hcl hpl key value
        (closed (initializeMarked right r)) cached
      have full := prepared.trans inserted
      simp only [initializeMarked,hp,Bool.false_eq_true,if_false]
      apply full.mono
      have hsize : (initializeMarked right l).core.size ≤ K := by
        rw [initializeMarked_size]; exact (skeleton_height right l).trans hl
      have hm := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
      simp only [Source.internalCount,Nat.mul_add,Nat.mul_one]
      omega
    · have inserted := prependMarked_charged key value (closed (initializeMarked right l))
        (initializeMarked right r) hcr hpr cached
      have full := prepared.trans inserted
      simp only [initializeMarked,hp,if_true]
      apply full.mono
      have hsize : (initializeMarked right r).core.size ≤ K := by
        rw [initializeMarked_size]; exact (skeleton_height right r).trans hr
      have hm := Nat.clog_monotone 2 (Nat.add_le_add_right hsize 1)
      simp only [Source.internalCount,Nat.mul_add,Nat.mul_one]
      omega

end TangoSquared.Paper20261030.BoundaryObservations
