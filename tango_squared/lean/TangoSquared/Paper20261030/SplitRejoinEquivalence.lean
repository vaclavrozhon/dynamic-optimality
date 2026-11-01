import TangoSquared.Paper20261030.ComponentPortWords
import TangoSquared.Paper20261030.AdjacentExposure

/-! Rejoining exact split fragments preserves component semantics.
The output balancing shape may differ from the input, but the complete
record word and every attached port agree. This justifies executable
join-based reconstruction without reversing a remembered split trace.
-/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata

variable {α κ : Type*} {β : κ → Type*}

theorem join_split_equivalent [Ord κ] [LawfulEqOrd κ]
    (component : AuxiliaryComponent α κ β) (key : κ) (found : searchResult key component.core = true) :
    Equivalent (join key (splitAt key component.core component.balanced found).value
      (cutLeft component key found) (cutRight component key found)) component := by
  apply equivalent_of_words
  · rw [join_word]
    exact splitAt_toList key component.core component.balanced found
  · rw [join_portWord,← cut_portWord]

theorem Equivalent.join [Ord κ] {left left' right right' : AuxiliaryComponent α κ β}
    (leftSame : Equivalent left left') (rightSame : Equivalent right right') (key : κ) (value : β key) :
    Equivalent (join key value left right) (join key value left' right') := by
  apply equivalent_of_words
  · simp only [join_word,leftSame.word,rightSame.word]
  · simp only [join_portWord,leftSame.portWord,rightSame.portWord]

theorem prepend_minimum_split_equivalent {γ : Nat → Type*} (component : AuxiliaryComponent α Nat γ)
    (ordered : component.core.Ordered) (key : Nat) (found : searchResult key component.core = true)
    (minimum : ∀ e ∈ component.core.toListModel, key ≤ e.1) :
    Equivalent (prepend key (splitAt key component.core component.balanced found).value
      (component.ports 0) (cutRight component key found)) component := by
  have empty := minimum_left_empty component ordered key found minimum
  apply equivalent_of_words
  · rw [prepend_word,← splitAt_toList key component.core component.balanced found]
    change _ = (cutLeft component key found).core.toListModel ++ _
    rw [empty,toListModel_leaf,List.nil_append]
    rfl
  · rw [prepend_portWord,cut_portWord component key found]
    have leftWord : (cutLeft component key found).portWord = [component.ports 0] := by
      simp only [portWord,empty,size_leaf,Nat.zero_add,List.range_one,List.map_singleton]
      rfl
    rw [leftWord,List.singleton_append]

end TangoSquared.Paper20261030.AuxiliaryComponent
