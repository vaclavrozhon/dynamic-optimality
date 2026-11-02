import ChaCha.Paper20261030.SplayAuxiliaryComponent

/-!
# Exact split and join of arbitrary-shape auxiliary components

These operations only assemble exposed cores and retain the same ordered
opaque port subtrees. Splaying supplies the charged exposure separately.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary.RawComponent

open DynamicOptimality (RawTree)
open ColoredStorage

variable {α κ : Type*}

def join (left : RawComponent α κ) (key : κ) (right : RawComponent α κ) : RawComponent α κ :=
  ⟨.node left.core key right.core,
    fun i => if i ≤ left.core.size then left.ports i else right.ports (i-(left.core.size+1))⟩

@[simp] theorem join_word (left : RawComponent α κ) (key : κ) (right : RawComponent α κ) :
    (join left key right).core.inorder = left.core.inorder ++ [key] ++ right.core.inorder := rfl

@[simp] theorem join_size (left : RawComponent α κ) (key : κ) (right : RawComponent α κ) :
    (join left key right).core.size = left.core.size+1+right.core.size := rfl

theorem join_closed (left : RawComponent α κ) (key : κ) (right : RawComponent α κ) :
    (join left key right).closed = Source.fork key left.closed right.closed := by
  change Source.fork key (GapSource.encode left.core (join left key right).ports 0)
    (GapSource.encode right.core (join left key right).ports (0+left.core.size+1)) = _
  have first : GapSource.encode left.core (join left key right).ports 0 = left.closed := by
    apply GapSource.encode_congr
    intro i lower upper
    simp only [Nat.zero_add] at upper
    simp only [join,if_pos upper]
  have shift : (fun i => (join left key right).ports (left.core.size+1+i)) = right.ports := by
    funext i
    have later : ¬ left.core.size+1+i ≤ left.core.size := by omega
    simp only [join,if_neg later,Nat.add_sub_cancel_left]
  rw [first]
  simp only [Nat.zero_add]
  rw [show left.core.size+1 = (left.core.size+1)+0 by omega,GapSource.encode_offset,shift]
  rfl

theorem join_portWord (left : RawComponent α κ) (key : κ) (right : RawComponent α κ) :
    (join left key right).portWord = left.portWord ++ right.portWord := by
  unfold portWord
  rw [join_size,show left.core.size+1+right.core.size+1 =
    (left.core.size+1)+(right.core.size+1) by omega,List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_inj_left.mpr
    intro i member
    have bound : i ≤ left.core.size := by have := List.mem_range.mp member; omega
    simp only [join,if_pos bound]
  · apply List.map_inj_left.mpr
    intro i member
    have later : ¬ left.core.size+1+i ≤ left.core.size := by omega
    simp only [Function.comp_def,join,if_neg later,Nat.add_sub_cancel_left]

def prefixPart (left : RawTree κ) (ports : Nat → Source α κ) : RawComponent α κ := ⟨left,ports⟩

def suffix (left right : RawTree κ) (ports : Nat → Source α κ) : RawComponent α κ :=
  ⟨right,fun i => ports (left.size+1+i)⟩

theorem split_join_equivalent (left right : RawTree κ) (key : κ) (ports : Nat → Source α κ) :
    Equivalent (join (prefixPart left ports) key (suffix left right ports)) ⟨.node left key right,ports⟩ := by
  refine ⟨rfl,?_⟩
  intro i bound
  by_cases first : i ≤ left.size
  · simp only [join,prefixPart,if_pos first]
  · simp only [join,prefixPart,suffix,if_neg first]
    congr 1
    omega

theorem split_portWord (left right : RawTree κ) (key : κ) (ports : Nat → Source α κ) :
    (RawComponent.mk (.node left key right) ports).portWord =
      (prefixPart left ports).portWord ++ (suffix left right ports).portWord := by
  rw [← (split_join_equivalent left right key ports).portWord,join_portWord]

theorem prefix_portWord (left right : RawTree κ) (key : κ) (ports : Nat → Source α κ) :
    (prefixPart left ports).portWord =
      (RawComponent.mk (.node left key right) ports).portWord.take (left.size+1) := by
  rw [split_portWord]
  simpa only [portWord_length,prefixPart] using
    (List.take_left (l₁ := (prefixPart left ports).portWord) (l₂ := (suffix left right ports).portWord)).symm

theorem suffix_portWord (left right : RawTree κ) (key : κ) (ports : Nat → Source α κ) :
    (suffix left right ports).portWord =
      (RawComponent.mk (.node left key right) ports).portWord.drop (left.size+1) := by
  rw [split_portWord]
  simpa only [portWord_length,prefixPart] using
    (List.drop_left (l₁ := (prefixPart left ports).portWord) (l₂ := (suffix left right ports).portWord)).symm

theorem prefix_suffix_closed (left right : RawTree κ) (key : κ) (ports : Nat → Source α κ) :
    (RawComponent.mk (.node left key right) ports).closed =
      Source.fork key (prefixPart left ports).closed (suffix left right ports).closed := by
  change Source.fork key (GapSource.encode left ports 0)
    (GapSource.encode right ports (0+left.size+1)) = _
  simp only [Nat.zero_add]
  rw [show left.size+1 = (left.size+1)+0 by omega,GapSource.encode_offset]
  rfl

end ChaCha.Paper20261030.SplayAuxiliary.RawComponent
