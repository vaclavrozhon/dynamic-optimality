import TangoSquared.Paper20261030.AuxiliaryComponents
import TangoSquared.Paper20261030.ChargedJoin

/-!
# Joining adjacent physical auxiliary components at an existing separator

The input fork already contains the separating record. The charged
balanced join incorporates both component skeletons, preserving the exact
concatenation of their gap ports. No key or record is allocated.
-/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*}

def join (key : κ) (value : β key) (l r : AuxiliaryComponent α κ β) : AuxiliaryComponent α κ β :=
  let joined := link key value l.core r.core l.balanced r.balanced
  ⟨joined.impl,joined.balanced_impl,
    fun i => if i ≤ l.core.size then l.ports i else r.ports (i - (l.core.size + 1))⟩

theorem join_size (key : κ) (value : β key) (l r : AuxiliaryComponent α κ β) :
    (join key value l r).core.size = l.core.size + 1 + r.core.size :=
  (link key value l.core r.core l.balanced r.balanced).size_impl

theorem join_word [Ord κ] (key : κ) (value : β key) (l r : AuxiliaryComponent α κ β) :
    (join key value l r).core.toListModel = l.core.toListModel ++ ⟨key,value⟩ :: r.core.toListModel := by
  simp only [join,toListModel_link]

theorem join_input (key : κ) (value : β key) (l r : AuxiliaryComponent α κ β) (old : Nat) :
    GapSource.encode (recordTree (.inner old key value l.core r.core))
      (join key value l r).ports 0 = .fork (old,⟨key,value⟩) l.tree r.tree := by
  simp only [recordTree,GapSource.encode,Nat.zero_add,recordTree_size_of_balanced l.core l.balanced]
  have hl : GapSource.encode (recordTree l.core) (join key value l r).ports 0 = l.tree := by
    apply GapSource.encode_congr
    intro i hlo hhi
    rw [Nat.zero_add,recordTree_size_of_balanced l.core l.balanced] at hhi
    simp only [join,if_pos hhi]
  have hr : GapSource.encode (recordTree r.core) (join key value l r).ports (l.core.size + 1) = r.tree := by
    have he : (fun i => (join key value l r).ports (l.core.size + 1 + i)) = r.ports := by
      funext i
      have hn : ¬ l.core.size + 1 + i ≤ l.core.size := by omega
      simp only [join,if_neg hn,Nat.add_sub_cancel_left]
    rw [show l.core.size + 1 = (l.core.size + 1) + 0 by omega,GapSource.encode_offset,he]
    rfl
  rw [hl,hr]

theorem join_charged (key : κ) (value : β key) (l r : AuxiliaryComponent α κ β) (old : Nat) :
    SourcePointer.Rearranges (.fork (old,⟨key,value⟩) l.tree r.tree) (join key value l r).tree
      (495 * (Nat.clog 2 (l.core.size + 1) + Nat.clog 2 (r.core.size + 1)) + 76) := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := link_charged_log old key value l.core r.core l.balanced r.balanced []
  have lifted := GapSource.metadata_trace trace (join key value l r).ports 0
  have rooted : SourcePointer.Trace ⟨.fork (old,⟨key,value⟩) l.tree r.tree,[]⟩ reads
      ⟨(join key value l r).tree,[]⟩ cost := by
    simp only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero] at lifted
    rw [join_input] at lifted
    exact lifted
  exact ⟨reads,cost,rooted.extend ancestors,hcost⟩

end TangoSquared.Paper20261030.AuxiliaryComponent
