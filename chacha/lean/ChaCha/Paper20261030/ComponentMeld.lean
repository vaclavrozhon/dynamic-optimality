import ChaCha.Paper20261030.ComponentCut
import ChaCha.Paper20261030.ComponentJoin

/-!
# Incorporating a component hanging in an extreme port

The separating record is already the extreme record of the outer core.
Expose it, then join its other child with the incoming component. This
incorporates all incoming records without creating a new separator.
The hypotheses identify the actual attachment and the empty side of
the split. Finding the extreme record is handled by `ExtremeSearch`.
-/

namespace ChaCha.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*} [Ord κ] [LawfulEqOrd κ]

def meldLast (outer incoming : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true) : AuxiliaryComponent α κ β :=
  join key (splitAt key outer.core outer.balanced found).value
    (cutLeft outer key found) incoming

def meldFirst (incoming outer : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true) : AuxiliaryComponent α κ β :=
  join key (splitAt key outer.core outer.balanced found).value
    incoming (cutRight outer key found)

theorem cutRight_empty_tree (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true)
    (empty : (splitAt key c.core c.balanced found).right = .leaf) :
    (cutRight c key found).tree = c.ports c.core.size := by
  have hs := splitAt_size key c.core c.balanced found
  simp only [empty,size_leaf,Nat.add_zero] at hs
  simpa only [cutRight,tree,empty,recordTree,GapSource.encode,Nat.add_zero,hs]

theorem cutLeft_empty_tree (c : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key c.core = true)
    (empty : (splitAt key c.core c.balanced found).left = .leaf) :
    (cutLeft c key found).tree = c.ports 0 := by
  simp only [cutLeft,tree,empty,recordTree,GapSource.encode]

theorem meldLast_word (outer incoming : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).right = .leaf) :
    (meldLast outer incoming key found).core.toListModel =
      outer.core.toListModel ++ incoming.core.toListModel := by
  rw [← splitAt_toList key outer.core outer.balanced found]
  simp only [meldLast,join_word,cutLeft,SplitResult.impl,bin,toListModel_inner,
    empty,toListModel_leaf,List.append_assoc,List.cons_append,List.nil_append]

theorem meldFirst_word (incoming outer : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).left = .leaf) :
    (meldFirst incoming outer key found).core.toListModel =
      incoming.core.toListModel ++ outer.core.toListModel := by
  rw [← splitAt_toList key outer.core outer.balanced found]
  simp only [meldFirst,join_word,cutRight,SplitResult.impl,bin,toListModel_inner,
    empty,toListModel_leaf,List.nil_append]

theorem meldLast_size (outer incoming : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).right = .leaf) :
    (meldLast outer incoming key found).core.size = outer.core.size + incoming.core.size := by
  have hs := splitAt_size key outer.core outer.balanced found
  simp only [empty,size_leaf,Nat.add_zero] at hs
  simp only [meldLast,join_size,cutLeft,hs]

theorem meldFirst_size (incoming outer : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).left = .leaf) :
    (meldFirst incoming outer key found).core.size = incoming.core.size + outer.core.size := by
  have hs := splitAt_size key outer.core outer.balanced found
  simp only [empty,size_leaf,Nat.zero_add] at hs
  simp only [meldFirst,join_size,cutRight]
  omega

theorem meldLast_charged (outer incoming : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).right = .leaf)
    (attached : outer.ports outer.core.size = incoming.tree) :
    SourcePointer.Rearranges outer.tree (meldLast outer incoming key found).tree
      (6225 * Nat.clog 2 (outer.core.size + 1) +
        495 * Nat.clog 2 (incoming.core.size + 1) + 76) := by
  have exposed := expose_charged outer key found
  rw [cutRight_empty_tree outer key found empty,attached] at exposed
  have joined := join_charged key (splitAt key outer.core outer.balanced found).value
    (cutLeft outer key found) incoming outer.core.size
  apply (exposed.trans joined).mono
  have hs := splitAt_size key outer.core outer.balanced found
  have hm := Nat.clog_monotone 2
    (show (cutLeft outer key found).core.size + 1 ≤ outer.core.size + 1 by
      change (splitAt key outer.core outer.balanced found).left.size + 1 ≤ _
      omega)
  omega

theorem meldFirst_charged (incoming outer : AuxiliaryComponent α κ β) (key : κ)
    (found : searchResult key outer.core = true)
    (empty : (splitAt key outer.core outer.balanced found).left = .leaf)
    (attached : outer.ports 0 = incoming.tree) :
    SourcePointer.Rearranges outer.tree (meldFirst incoming outer key found).tree
      (6225 * Nat.clog 2 (outer.core.size + 1) +
        495 * Nat.clog 2 (incoming.core.size + 1) + 76) := by
  have exposed := expose_charged outer key found
  rw [cutLeft_empty_tree outer key found empty,attached] at exposed
  have joined := join_charged key (splitAt key outer.core outer.balanced found).value
    incoming (cutRight outer key found) outer.core.size
  apply (exposed.trans joined).mono
  have hs := splitAt_size key outer.core outer.balanced found
  have hm := Nat.clog_monotone 2
    (show (cutRight outer key found).core.size + 1 ≤ outer.core.size + 1 by
      change (splitAt key outer.core outer.balanced found).right.size + 1 ≤ _
      omega)
  omega

end ChaCha.Paper20261030.AuxiliaryComponent
