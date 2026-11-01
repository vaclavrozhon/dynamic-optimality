import TangoSquared.Paper20261030.BoundaryContext

/-!
# Lifting an actual descendant repair through its preferred context

All four boundary cases are handled: two separators, one on either side,
or no outside records. A physical repair of any representation of the
descendant lifts to the whole representation with logarithmic overhead.
The same semantic context represents the changed reference afterwards.
-/

namespace TangoSquared.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α : Type*} {β : Nat → Type*} {right : Record (β := β) → Bool}

theorem repair_context (oldSource newSource : Source α (Record (β := β)))
    (sub c : AuxiliaryComponent α Nat (Tagged β)) (frames : List (ContextFrame right))
    (representedSub : Represents right oldSource sub)
    (same : Equivalent c (PreferredContext.wrap sub frames)) (ordered : c.core.Ordered)
    (repairCost : Nat)
    (repair : ∀ actual : AuxiliaryComponent α Nat (Tagged β), Represents right oldSource actual →
      ∃ fresh : AuxiliaryComponent α Nat (Tagged β), Represents right newSource fresh ∧
        SourcePointer.Rearranges (closed actual) (closed fresh) repairCost)
    (K : Nat) (hold : c.core.size ≤ K)
    (hnew : (PreferredContext.plug newSource frames).shape.height ≤ K) :
    ∃ out : AuxiliaryComponent α Nat (Tagged β),
      Represents right (PreferredContext.plug newSource frames) out ∧
      SourcePointer.Rearranges (closed c) (closed out)
        (repairCost + 13440 * Nat.clog 2 (K + 1) + 176) := by
  have represented := (PreferredContext.represents frames representedSub).equivalent same
  obtain ⟨hc,hp⟩ := represented.invariant
  cases last : (PreferredContext.before frames).getLast? with
  | none =>
    have hb := List.getLast?_eq_none_iff.mp last
    cases ha : PreferredContext.after frames with
    | nil =>
      have eqSub := same.trans (empty_context sub frames hb ha).symm
      obtain ⟨fresh,hfresh,trace⟩ := repair c (representedSub.equivalent eqSub)
      have hout := (PreferredContext.represents frames hfresh).equivalent (empty_context fresh frames hb ha)
      exact ⟨fresh,hout,trace.mono (by omega)⟩
    | cons hi after =>
      obtain ⟨found,eqSub,rejoin⟩ := prefix_context c sub frames same ordered after hi hb ha
      obtain ⟨fresh,hfresh,trace⟩ := repair (cutLeft c hi.1 found) (representedSub.equivalent eqSub)
      have hout := (PreferredContext.represents frames hfresh).equivalent (rejoin fresh)
      obtain ⟨hfc,hfp⟩ := hfresh.invariant
      have charged := replacePrefix_charged c hc hp hi.1 found fresh hfc hfp repairCost trace K hold
        (hout.size_height.trans hnew)
      exact ⟨_,hout,charged.mono (by omega)⟩
  | some lo =>
    obtain ⟨before,hb⟩ := List.getLast?_eq_some_iff.mp last
    cases ha : PreferredContext.after frames with
    | nil =>
      obtain ⟨found,eqSub,rejoin⟩ := suffix_context c sub frames same ordered before lo hb ha
      obtain ⟨fresh,hfresh,trace⟩ := repair (cutRight c lo.1 found) (representedSub.equivalent eqSub)
      have hout := (PreferredContext.represents frames hfresh).equivalent (rejoin fresh)
      obtain ⟨hfc,hfp⟩ := hfresh.invariant
      have charged := replaceSuffix_charged c hc hp lo.1 found fresh hfc hfp repairCost trace K hold
        (hout.size_height.trans hnew)
      exact ⟨_,hout,charged.mono (by omega)⟩
    | cons hi after =>
      obtain ⟨fl,fh,eqSub,rejoin⟩ := middle_context c sub frames same ordered before after lo hi hb ha
      obtain ⟨fresh,hfresh,trace⟩ := repair (middle c lo.1 fl hi.1 fh) (representedSub.equivalent eqSub)
      have hout := (PreferredContext.represents frames hfresh).equivalent (rejoin fresh)
      obtain ⟨hfc,hfp⟩ := hfresh.invariant
      exact ⟨_,hout,replaceMiddle_charged c hc hp lo.1 fl hi.1 fh fresh hfc hfp repairCost trace K hold
        (hout.size_height.trans hnew)⟩

end TangoSquared.Paper20261030.PathDecomposition
