import TangoSquared.Paper20261030.BoundaryObservations

/-!
# Opening and closing a physically marked auxiliary component

The core stores false entry bits. Its closed physical representation
marks the current root true, while all hanging port roots are marked
true already. Opening a nonempty component clears the reached root bit;
closing marks the new root. Each change is an actual read and write.
Payload-preserving auxiliary rearrangements retain the core's false bits.
-/

namespace TangoSquared.Paper20261030.BoundaryObservations

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata SourcePointer

variable {α κ : Type*} {β : κ → Type*}

def tag (bit : Bool) (record : Record (β := β)) : Record (β := β) :=
  (record.1,⟨record.2.1,(record.2.2.1,bit)⟩)

theorem tag_entry (bit : Bool) (record : Record (β := β)) : entry (tag bit record) = bit := rfl

theorem tag_same (record : Record (β := β)) : tag (entry record) record = record := by
  rcases record with ⟨cached,⟨key,value,bit⟩⟩
  rfl

theorem tag_tag (a b : Bool) (record : Record (β := β)) : tag a (tag b record) = tag a record := rfl

theorem clean_iff_word (t : Impl κ (Tagged β)) :
    Clean t ↔ ∀ e ∈ t.toListModel, e.2.2 = false := by
  induction t with
  | leaf => simp [Clean,toListModel]
  | inner cached key value l r ihl ihr =>
    simp only [Clean,ihl,ihr,toListModel_inner,List.mem_append,List.mem_cons]
    constructor
    · rintro ⟨hv,hl,hr⟩ e (he | he | he)
      · exact hl e he
      · cases he; exact hv
      · exact hr e he
    · intro h
      exact ⟨h _ (Or.inr (Or.inl rfl)),fun e he => h e (Or.inl he),fun e he => h e (Or.inr (Or.inr he))⟩

theorem clean_of_word {t u : Impl κ (Tagged β)} (ht : Clean t) (he : u.toListModel = t.toListModel) : Clean u := by
  rw [clean_iff_word,he]
  exact (clean_iff_word t).mp ht

def MarkedPorts (c : AuxiliaryComponent α κ (Tagged β)) : Prop :=
  ∀ i, i ≤ c.core.size → entry (c.ports i).rootRecord = true

def closed (c : AuxiliaryComponent α κ (Tagged β)) : Source α (Record (β := β)) :=
  c.tree.setRoot (tag true c.tree.rootRecord)

theorem closed_entry (c : AuxiliaryComponent α κ (Tagged β)) : entry (closed c).rootRecord = true := by
  unfold closed
  cases c.tree <;> rfl

theorem open_entry (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core) (hne : c.core ≠ .leaf) :
    entry c.tree.rootRecord = false := by
  rcases c with ⟨core,balanced,ports⟩
  cases core with
  | leaf => contradiction
  | inner cached key value l r => exact hc.1

theorem closed_terminal (c : AuxiliaryComponent α κ (Tagged β)) (hc : c.core = .leaf)
    (hp : MarkedPorts c) : closed c = c.tree := by
  have he : entry c.tree.rootRecord = true := by
    have hz := hp 0 (by omega)
    simpa only [AuxiliaryComponent.tree,hc,recordTree,GapSource.encode] using hz
  unfold closed
  rw [← he,tag_same]
  cases c.tree <;> rfl

theorem open_charged (c : AuxiliaryComponent α κ (Tagged β)) (hc : Clean c.core) (hp : MarkedPorts c) :
    SourcePointer.Rearranges (closed c) c.tree 2 := by
  by_cases he : c.core = .leaf
  · rw [closed_terminal c he hp]
    exact SourcePointer.rearranges_refl _ _
  · have hb := open_entry c hc he
    have ht : (closed c).setRoot (tag false (closed c).rootRecord) = c.tree := by
      unfold closed
      have htag : tag false c.tree.rootRecord = c.tree.rootRecord := by rw [← hb,tag_same]
      cases htree : c.tree <;>
        simpa only [htree,Source.setRoot,Source.rootRecord,tag_tag] using congrArg (fun v =>
          (c.tree.setRoot v)) htag
    intro ancestors
    have trace := SourcePointer.write_charged (closed c) (tag false (closed c).rootRecord) ancestors
    exact ⟨_,2,by simpa only [ht] using trace,le_rfl⟩

theorem close_charged (c : AuxiliaryComponent α κ (Tagged β)) :
    SourcePointer.Rearranges c.tree (closed c) 2 := SourcePointer.replace_root _ _

theorem observe_component (depth : Nat) (c : AuxiliaryComponent α κ (Tagged β))
    (hc : Clean c.core) (hp : MarkedPorts c) (ancestors) :
    ∃ reads cost,
      SourcePointer.Trace ⟨c.tree,ancestors⟩ reads ⟨c.tree,ancestors⟩ cost ∧
      (∀ tail, parse depth (reads ++ tail) = some (capture depth c.core,tail)) ∧
      cost ≤ 5 * (2 ^ depth - 1) := by
  apply observe depth c.core hc c.ports 0 _ ancestors
  intro i hlo hhi
  apply hp i
  simpa only [Nat.zero_add,recordTree_size_of_balanced c.core c.balanced] using hhi

end TangoSquared.Paper20261030.BoundaryObservations
