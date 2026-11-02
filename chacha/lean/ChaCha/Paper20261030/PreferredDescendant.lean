import ChaCha.Paper20261030.PreferredContext

/-!
# Exposing the semantic context of a preferred descendant

This theorem extracts the represented descendant component and the exact
unchanged ancestor context. The descendant word is contiguous in the
whole auxiliary word, and its actual ports form the corresponding window.
It is a decomposition theorem; the logarithmic physical exposure is given
by the charged interval operations.
-/

namespace ChaCha.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α κ : Type*} {β : κ → Type*}

inductive PreferredDescendant (right : Record (β := β) → Bool) :
    Source α (Record (β := β)) → Source α (Record (β := β)) → Prop
  | refl (source) : PreferredDescendant right source source
  | left {record l r sub} (direction : right record = false)
      (below : PreferredDescendant right l sub) : PreferredDescendant right (.fork record l r) sub
  | right {record l r sub} (direction : right record = true)
      (below : PreferredDescendant right r sub) : PreferredDescendant right (.fork record l r) sub

theorem PreferredDescendant.context [Ord κ] {right : Record (β := β) → Bool}
    {reference subtree : Source α (Record (β := β))}
    (below : PreferredDescendant right reference subtree)
    (c : AuxiliaryComponent α κ (Tagged β)) (represented : Represents right reference c) :
    ∃ (sub : AuxiliaryComponent α κ (Tagged β)) (frames : List (ContextFrame right)),
      Represents right subtree sub ∧ Equivalent c (PreferredContext.wrap sub frames) ∧
        PreferredContext.plug subtree frames = reference := by
  induction below generalizing c with
  | refl reference => exact ⟨c,[],represented,.refl _,rfl⟩
  | @left record l r subtree direction below ih =>
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.left_view direction
    obtain ⟨sub,frames,hs,he,hplug⟩ := ih lc hl
    let frame : ContextFrame right := .left record r rc represented.raw.1 direction hr
    refine ⟨sub,frames ++ [frame],hs,?_,?_⟩
    · rw [PreferredContext.wrap_append]
      exact same.trans (frame.equivalent he)
    · rw [PreferredContext.plug_append]
      change frame.applyReference (PreferredContext.plug subtree frames) = _
      rw [hplug]
      rfl
  | @right record l r subtree direction below ih =>
    obtain ⟨lc,rc,hl,hr,same⟩ := represented.right_view direction
    obtain ⟨sub,frames,hs,he,hplug⟩ := ih rc hr
    let frame : ContextFrame right := .right record l lc represented.raw.1 direction hl
    refine ⟨sub,frames ++ [frame],hs,?_,?_⟩
    · rw [PreferredContext.wrap_append]
      exact same.trans (frame.equivalent he)
    · rw [PreferredContext.plug_append]
      change frame.applyReference (PreferredContext.plug subtree frames) = _
      rw [hplug]
      rfl

theorem PreferredDescendant.word_ports [Ord κ] {right : Record (β := β) → Bool}
    {reference subtree : Source α (Record (β := β))}
    (below : PreferredDescendant right reference subtree)
    (c : AuxiliaryComponent α κ (Tagged β)) (represented : Represents right reference c) :
    ∃ (sub : AuxiliaryComponent α κ (Tagged β)) (frames : List (ContextFrame right)),
      Represents right subtree sub ∧
      c.core.toListModel = PreferredContext.before frames ++ sub.core.toListModel ++ PreferredContext.after frames ∧
      (∀ i, i ≤ sub.core.size → c.ports ((PreferredContext.before frames).length + i) = sub.ports i) ∧
      PreferredContext.plug subtree frames = reference := by
  obtain ⟨sub,frames,hs,he,hplug⟩ := below.context c represented
  refine ⟨sub,frames,hs,he.word.trans (PreferredContext.word sub frames),?_,hplug⟩
  intro i hi
  have hb : (PreferredContext.before frames).length + i ≤ c.core.size := by
    rw [he.size,PreferredContext.size]
    have := PreferredContext.before_length frames
    omega
  rw [he.ports _ hb]
  exact PreferredContext.port_window sub frames i hi

end ChaCha.Paper20261030.PathDecomposition
