import TangoSquared.Paper20261030.PathInitialization
import TangoSquared.Paper20261030.ProjectionLocal

/-!
# Balanced auxiliary components with their actual gap subtrees

Each component consists of a balanced separator skeleton and its hanging
ports. Adding a new minimum or maximum separator uses the verified
charged insertion, preserving all existing ports and attaching one new
sibling subtree. The input is the actual fork at the new separator.
-/

namespace TangoSquared.Paper20261030.Auxiliary.Metadata

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl

variable {κ : Type*} {β : κ → Type*}

theorem recordTree_size (t : Impl κ β) : (recordTree t).size = actualSize t := by
  induction t <;> simp_all [recordTree,MTR.Tree.size,actualSize]

theorem recordTree_size_of_balanced (t : Impl κ β) (ht : t.Balanced) :
    (recordTree t).size = t.size := by
  rw [recordTree_size,actualSize_length,← size_eq_length t ht]

end TangoSquared.Paper20261030.Auxiliary.Metadata

namespace TangoSquared.Paper20261030

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

structure AuxiliaryComponent (α κ : Type*) (β : κ → Type*) where
  core : Impl κ β
  balanced : core.Balanced
  ports : Nat → Source α (NodeRecord κ β)

namespace AuxiliaryComponent

variable {α κ : Type*} {β : κ → Type*}

def tree (c : AuxiliaryComponent α κ β) : Source α (NodeRecord κ β) :=
  GapSource.encode (recordTree c.core) c.ports 0

def terminal (port : Source α (NodeRecord κ β)) : AuxiliaryComponent α κ β :=
  ⟨.leaf,.leaf,fun _ => port⟩

def prepend (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) : AuxiliaryComponent α κ β :=
  let result := insertMin key value c.core c.balanced
  ⟨result.impl,result.balanced_impl,fun i => if i = 0 then sibling else c.ports (i - 1)⟩

def append (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) : AuxiliaryComponent α κ β :=
  let result := insertMax key value c.core c.balanced
  ⟨result.impl,result.balanced_impl,fun i => if i ≤ c.core.size then c.ports i else sibling⟩

theorem prepend_size (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) : (prepend key value sibling c).core.size = c.core.size + 1 := by
  simpa only [prepend,Nat.add_comm] using (insertMin key value c.core c.balanced).size_impl

theorem append_size (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) : (append c key value sibling).core.size = c.core.size + 1 :=
  (insertMax key value c.core c.balanced).size_impl

theorem prepend_word [Ord κ] (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) :
    (prepend key value sibling c).core.toListModel = ⟨key,value⟩ :: c.core.toListModel := by
  simp only [prepend,toListModel_insertMin]

theorem append_word [Ord κ] (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) :
    (append c key value sibling).core.toListModel = c.core.toListModel ++ [⟨key,value⟩] := by
  simp only [append,toListModel_insertMax]

theorem prepend_input (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) (old : Nat) :
    GapSource.encode (recordTree (.inner old key value .leaf c.core))
      (prepend key value sibling c).ports 0 = .fork (old,⟨key,value⟩) sibling c.tree := by
  simp only [recordTree,GapSource.encode,MTR.Tree.size,Nat.zero_add]
  have hl : (prepend key value sibling c).ports 0 = sibling := by simp [prepend]
  have hr : GapSource.encode (recordTree c.core) (prepend key value sibling c).ports 1 = c.tree := by
    have he : (fun i => (prepend key value sibling c).ports (1 + i)) = c.ports := by
      funext i
      simp [prepend,Nat.add_comm]
    rw [show 1 = 1 + 0 by rfl,GapSource.encode_offset,he]
    rfl
  rw [hl,hr]

theorem append_input (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) (old : Nat) :
    GapSource.encode (recordTree (.inner old key value c.core .leaf))
      (append c key value sibling).ports 0 = .fork (old,⟨key,value⟩) c.tree sibling := by
  simp only [recordTree,GapSource.encode,Nat.zero_add]
  have hl : GapSource.encode (recordTree c.core) (append c key value sibling).ports 0 = c.tree := by
    apply GapSource.encode_congr
    intro i hlo hhi
    rw [Nat.zero_add,recordTree_size_of_balanced c.core c.balanced] at hhi
    simp only [append,if_pos hhi]
  have hr : (append c key value sibling).ports ((recordTree c.core).size + 1) = sibling := by
    rw [recordTree_size_of_balanced c.core c.balanced]
    simp [append]
  rw [hl,hr]

theorem prepend_charged (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (c : AuxiliaryComponent α κ β) (old : Nat) :
    SourcePointer.Rearranges (.fork (old,⟨key,value⟩) sibling c.tree)
      (prepend key value sibling c).tree (495 * Nat.clog 2 (c.core.size + 1) + 76) := by
  intro rest
  obtain ⟨reads,cost,trace,hcost⟩ := insertMin_charged_log old key value c.core c.balanced []
  have lifted := GapSource.metadata_trace trace (prepend key value sibling c).ports 0
  have rooted : SourcePointer.Trace ⟨.fork (old,⟨key,value⟩) sibling c.tree,[]⟩ reads
      ⟨(prepend key value sibling c).tree,[]⟩ cost := by
    simp only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero] at lifted
    rw [prepend_input] at lifted
    exact lifted
  exact ⟨reads,cost,rooted.extend rest,hcost⟩

theorem append_charged (c : AuxiliaryComponent α κ β) (key : κ) (value : β key)
    (sibling : Source α (NodeRecord κ β)) (old : Nat) :
    SourcePointer.Rearranges (.fork (old,⟨key,value⟩) c.tree sibling)
      (append c key value sibling).tree (495 * Nat.clog 2 (c.core.size + 1) + 76) := by
  intro rest
  obtain ⟨reads,cost,trace,hcost⟩ := insertMax_charged_log old key value c.core c.balanced []
  have lifted := GapSource.metadata_trace trace (append c key value sibling).ports 0
  have rooted : SourcePointer.Trace ⟨.fork (old,⟨key,value⟩) c.tree sibling,[]⟩ reads
      ⟨(append c key value sibling).tree,[]⟩ cost := by
    simp only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero] at lifted
    rw [append_input] at lifted
    exact lifted
  exact ⟨reads,cost,rooted.extend rest,hcost⟩

end AuxiliaryComponent

end TangoSquared.Paper20261030
