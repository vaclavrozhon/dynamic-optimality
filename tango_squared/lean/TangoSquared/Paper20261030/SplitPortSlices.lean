import TangoSquared.Paper20261030.ExactSplitWords
import TangoSquared.Paper20261030.ComponentPortWords

/-! A successful split recovers both specified record slices and both
specified port slices. The split position is the number of lower records,
so equality of the complete port lists determines each resulting list. -/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α : Type*} {β : Nat → Type*}

theorem cutLeft_ordered (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (key : Nat) (found : searchResult key c.core = true) : (cutLeft c key found).core.Ordered := by
  have ho := splitAt_ordered key c.core c.balanced found ordered
  change ((splitAt key c.core c.balanced found).left.toListModel ++
    ⟨key,(splitAt key c.core c.balanced found).value⟩ ::
      (splitAt key c.core c.balanced found).right.toListModel).Pairwise _ at ho
  exact (List.pairwise_append.mp ho).1

theorem cutRight_ordered (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (key : Nat) (found : searchResult key c.core = true) : (cutRight c key found).core.Ordered := by
  have ho := splitAt_ordered key c.core c.balanced found ordered
  change ((splitAt key c.core c.balanced found).left.toListModel ++
    ⟨key,(splitAt key c.core c.balanced found).value⟩ ::
      (splitAt key c.core c.balanced found).right.toListModel).Pairwise _ at ho
  exact (List.pairwise_cons.mp (List.pairwise_append.mp ho).2.1).2

theorem split_slices (c : AuxiliaryComponent α Nat β) (ordered : c.core.Ordered)
    (before after : List (Sigma β)) (pivot : Sigma β)
    (beforePorts afterPorts : List (Source α (NodeRecord Nat β)))
    (word : c.core.toListModel = before ++ pivot :: after)
    (ports : c.portWord = beforePorts ++ afterPorts)
    (portLength : beforePorts.length = before.length + 1)
    (found : searchResult pivot.1 c.core = true) :
    (cutLeft c pivot.1 found).core.toListModel = before ∧
      (⟨pivot.1,(splitAt pivot.1 c.core c.balanced found).value⟩ : Sigma β) = pivot ∧
      (cutRight c pivot.1 found).core.toListModel = after ∧
      (cutLeft c pivot.1 found).portWord = beforePorts ∧
      (cutRight c pivot.1 found).portWord = afterPorts := by
  obtain ⟨hl,hv,hr⟩ := splitAt_word_decomposition c.core c.balanced ordered before after pivot word found
  have hp := (cut_portWord c pivot.1 found).symm.trans ports
  have hlen : (cutLeft c pivot.1 found).portWord.length = beforePorts.length := by
    rw [portWord_length,size_eq_length _ (cutLeft c pivot.1 found).balanced,portLength]
    change (splitAt pivot.1 c.core c.balanced found).left.toListModel.length + 1 = _
    rw [hl]
  obtain ⟨hpl,hpr⟩ := List.append_inj hp hlen
  exact ⟨hl,hv,hr,hpl,hpr⟩

end TangoSquared.Paper20261030.AuxiliaryComponent
