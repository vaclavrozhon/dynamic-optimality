import TangoSquared.Paper20261030.AuxiliaryComponents
import TangoSquared.Paper20261030.ChargedSplit
import TangoSquared.Paper20261030.AuxiliarySemantics

/-!
# Physically cutting a balanced auxiliary at a stored separator

Expose the separator, retain its greater keys as a balanced suffix
component, and rebalance the lesser keys together with the separator.
The suffix is attached as the last gap of the balanced prefix component.
All original hanging subtrees retain their order and contents. The
source trace includes the changes to cached auxiliary sizes.

Application flags that mark the two component entries are not changed by
this primitive; their charged updates belong to the caller.
-/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

def cutLeft (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    AuxiliaryComponent α κ β :=
  let s := splitAt key c.core c.balanced found
  ⟨s.left,s.left_balanced,c.ports⟩

def cutRight (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    AuxiliaryComponent α κ β :=
  let s := splitAt key c.core c.balanced found
  ⟨s.right,s.right_balanced,fun i => c.ports (s.left.size + 1 + i)⟩

def cutOutput (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    AuxiliaryComponent α κ β :=
  (cutLeft c key found).append key (splitAt key c.core c.balanced found).value (cutRight c key found).tree

theorem cutOutput_last_port (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true) :
    (cutOutput c key found).ports (cutOutput c key found).core.size = (cutRight c key found).tree := by
  unfold cutOutput
  rw [append_size]
  simp only [append,show ¬ (cutLeft c key found).core.size + 1 ≤ (cutLeft c key found).core.size by omega,
    if_false]

theorem cutRight_last_port (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true) :
    (cutRight c key found).ports (cutRight c key found).core.size = c.ports c.core.size := by
  simp only [cutRight,splitAt_size key c.core c.balanced found]

theorem cutOutput_size_le (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true) : (cutOutput c key found).core.size ≤ c.core.size := by
  have hs := splitAt_size key c.core c.balanced found
  simp only [cutOutput,append_size,cutLeft]
  omega

theorem cutRight_size_le (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true) : (cutRight c key found).core.size ≤ c.core.size := by
  have hs := splitAt_size key c.core c.balanced found
  simp only [cutRight]
  omega

theorem cut_word (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    (cutOutput c key found).core.toListModel ++ (cutRight c key found).core.toListModel =
      c.core.toListModel := by
  have he := splitAt_toList key c.core c.balanced found
  simpa only [cutOutput,append_word,cutLeft,cutRight,SplitResult.impl,bin,toListModel_inner,
    List.append_assoc,List.singleton_append] using he

theorem cut_exposed_tree (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    GapSource.encode (recordTree (splitAt key c.core c.balanced found).impl) c.ports 0 =
      .fork (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
        (cutLeft c key found).tree (cutRight c key found).tree := by
  let s := splitAt key c.core c.balanced found
  have hs : s.left.size + 1 + s.right.size = c.core.size := splitAt_size key c.core c.balanced found
  have he : GapSource.encode (recordTree s.right) c.ports (s.left.size + 1) =
      (cutRight c key found).tree := by
    rw [show s.left.size + 1 = (s.left.size + 1) + 0 by omega,GapSource.encode_offset]
    rfl
  change GapSource.encode (recordTree s.impl) c.ports 0 = _
  simp only [SplitResult.impl,bin,recordTree,GapSource.encode,
    recordTree_size_of_balanced s.left s.left_balanced,Nat.zero_add,hs,he]
  rfl

theorem expose_charged (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    SourcePointer.Rearranges c.tree
      (.fork (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
        (cutLeft c key found).tree (cutRight c key found).tree)
      (5730 * Nat.clog 2 (c.core.size + 1)) := by
  intro ancestors
  obtain ⟨reads,cost,trace,hcost⟩ := splitAt_charged_log key c.core c.balanced found []
  have lifted := GapSource.metadata_trace trace c.ports 0
  have rooted : SourcePointer.Trace ⟨c.tree,[]⟩ reads
      ⟨.fork (c.core.size,⟨key,(splitAt key c.core c.balanced found).value⟩)
        (cutLeft c key found).tree (cutRight c key found).tree,[]⟩ cost := by
    simp only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero] at lifted
    rw [cut_exposed_tree] at lifted
    exact lifted
  exact ⟨reads,cost,rooted.extend ancestors,hcost⟩

theorem cut_charged (c : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key c.core = true) :
    SourcePointer.Rearranges c.tree (cutOutput c key found).tree
      (6225 * Nat.clog 2 (c.core.size + 1) + 76) := by
  let s := splitAt key c.core c.balanced found
  have exposed := expose_charged c key found
  have joined := append_charged (cutLeft c key found) key s.value (cutRight c key found).tree c.core.size
  have full := exposed.trans joined
  apply full.mono
  have hs : s.left.size + 1 + s.right.size = c.core.size := splitAt_size key c.core c.balanced found
  have hm := Nat.clog_monotone 2
    (show (cutLeft c key found).core.size + 1 ≤ c.core.size + 1 by
      change s.left.size + 1 ≤ _
      omega)
  omega

end TangoSquared.Paper20261030.AuxiliaryComponent
