import TangoSquared.Paper20261030.ComponentMeld
import TangoSquared.Paper20261030.ComponentMarkers

/-!
# Semantic equality of balanced auxiliary components

Equivalent components have the same ordered record word and the same
actual subtree in each valid gap. Their balancing shapes and cached sizes
may differ. This relation lets the maintained reference decomposition
survive the physical balancing operations.
-/

namespace TangoSquared.Paper20261030.AuxiliaryComponent

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata BoundaryObservations

variable {α κ : Type*} {β : κ → Type*}

structure Equivalent (a b : AuxiliaryComponent α κ β) : Prop where
  word : a.core.toListModel = b.core.toListModel
  ports : ∀ i, i ≤ a.core.size → a.ports i = b.ports i

theorem Equivalent.size {a b : AuxiliaryComponent α κ β} (h : Equivalent a b) : a.core.size = b.core.size := by
  rw [size_eq_length a.core a.balanced,size_eq_length b.core b.balanced,h.word]

theorem Equivalent.refl (a : AuxiliaryComponent α κ β) : Equivalent a a := ⟨rfl,fun _ _ => rfl⟩

theorem Equivalent.symm {a b : AuxiliaryComponent α κ β} (h : Equivalent a b) : Equivalent b a :=
  ⟨h.word.symm,fun i hi => (h.ports i (by rw [h.size]; exact hi)).symm⟩

theorem Equivalent.trans {a b c : AuxiliaryComponent α κ β} (h : Equivalent a b) (g : Equivalent b c) :
    Equivalent a c :=
  ⟨h.word.trans g.word,fun i hi => (h.ports i hi).trans (g.ports i (by rw [← h.size]; exact hi))⟩

theorem Equivalent.clean {γ : κ → Type*} {a b : AuxiliaryComponent α κ (Tagged γ)}
    (h : Equivalent a b) (hb : Clean b.core) : Clean a.core := clean_of_word hb h.word

theorem Equivalent.marked {γ : κ → Type*} {a b : AuxiliaryComponent α κ (Tagged γ)}
    (h : Equivalent a b) (hb : MarkedPorts b) : MarkedPorts a := by
  intro i hi
  rw [h.ports i hi]
  exact hb i (by rw [← h.size]; exact hi)

theorem Equivalent.ordered [Ord κ] {a b : AuxiliaryComponent α κ β}
    (h : Equivalent a b) (hb : b.core.Ordered) : a.core.Ordered := by
  simpa only [Impl.Ordered,h.word] using hb

theorem Equivalent.append [Ord κ] {a b : AuxiliaryComponent α κ β}
    (h : Equivalent a b) (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β)) :
    Equivalent (append a key value sibling) (append b key value sibling) := by
  refine ⟨by simp only [append_word,h.word],?_⟩
  intro i hi
  by_cases ha : i ≤ a.core.size
  · have hb : i ≤ b.core.size := by rw [← h.size]; exact ha
    simpa only [AuxiliaryComponent.append,if_pos ha,if_pos hb] using h.ports i ha
  · have hb : ¬ i ≤ b.core.size := by rw [← h.size]; exact ha
    simp only [AuxiliaryComponent.append,if_neg ha,if_neg hb]

theorem Equivalent.prepend [Ord κ] {a b : AuxiliaryComponent α κ β}
    (h : Equivalent a b) (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β)) :
    Equivalent (prepend key value sibling a) (prepend key value sibling b) := by
  refine ⟨by simp only [prepend_word,h.word],?_⟩
  intro i hi
  by_cases hz : i = 0
  · simp only [AuxiliaryComponent.prepend,if_pos hz]
  · have hb : i - 1 ≤ a.core.size := by rw [prepend_size] at hi; omega
    simpa only [AuxiliaryComponent.prepend,if_neg hz] using h.ports (i - 1) hb

theorem max_left_equivalent [Ord κ] [LawfulEqOrd κ]
    (c l : AuxiliaryComponent α κ β) (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (he : Equivalent c (append l key value sibling))
    (found : searchResult key c.core = true)
    (empty : (splitAt key c.core c.balanced found).right = .leaf) :
    Equivalent (cutLeft c key found) l := by
  have hw := he.word
  rw [append_word,← splitAt_toList key c.core c.balanced found] at hw
  simp only [SplitResult.impl,bin,toListModel_inner,empty,toListModel_leaf] at hw
  have hword := List.append_inj_left' hw rfl
  have hs : (cutLeft c key found).core.size = l.core.size := by
    rw [size_eq_length _ (cutLeft c key found).balanced,size_eq_length _ l.balanced]
    exact congrArg List.length hword
  refine ⟨hword,?_⟩
  intro i hi
  have hb : i ≤ c.core.size := by
    have hsize := splitAt_size key c.core c.balanced found
    change i ≤ (splitAt key c.core c.balanced found).left.size at hi
    omega
  have hp := he.ports i hb
  have hil : i ≤ l.core.size := by rw [← hs]; exact hi
  simpa only [cutLeft,append,if_pos hil] using hp

theorem min_right_equivalent [Ord κ] [LawfulEqOrd κ]
    (c r : AuxiliaryComponent α κ β) (key : κ) (value : β key) (sibling : Source α (NodeRecord κ β))
    (he : Equivalent c (prepend key value sibling r))
    (found : searchResult key c.core = true)
    (empty : (splitAt key c.core c.balanced found).left = .leaf) :
    Equivalent (cutRight c key found) r := by
  have hw := he.word
  rw [prepend_word,← splitAt_toList key c.core c.balanced found] at hw
  simp only [SplitResult.impl,bin,toListModel_inner,empty,toListModel_leaf,List.nil_append] at hw
  have hword := (List.cons.inj hw).2
  refine ⟨hword,?_⟩
  intro i hi
  have hsize := splitAt_size key c.core c.balanced found
  have hp := he.ports (i + 1) (by
    change i ≤ (splitAt key c.core c.balanced found).right.size at hi
    simp only [empty,size_leaf,Nat.zero_add] at hsize
    omega)
  simpa only [cutRight,empty,size_leaf,Nat.zero_add,prepend,
    Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel,Nat.add_comm] using hp

end TangoSquared.Paper20261030.AuxiliaryComponent
