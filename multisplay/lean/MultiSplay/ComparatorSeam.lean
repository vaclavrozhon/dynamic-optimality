import ChaCha.Paper20261030.BoundaryContext
import ChaCha.Paper20261030.SourceReversal

/-!
# Removing and restoring the suffix boundary seam

An all-left preferred context may keep its final continuation in a separate
balanced auxiliary. Its administrative root core contains only the context
records, and its first gap contains the actual closed continuation. Merging
the two cores, or separating them again, uses an existing boundary record
and one balanced split/join. No leaf, separator key, or memory record is
created, and every off-path component is retained literally.
-/

namespace MultiSplay.ComparatorSeam

open ChaCha.Paper20261030
open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations PathDecomposition

variable {α : Type*} {β : Nat → Type*} {right : Record (β := β) → Bool}

/-- Closing an empty administrative core already containing a closed
component does not add a physical vertex or change its stored records. -/
theorem terminal_closed (component : AuxiliaryComponent α Nat (Tagged β)) :
    closed (terminal (closed component)) = closed component := by
  rw [closed_terminal _ rfl (fun _ _ => closed_entry component)]
  rfl

theorem equivalent_terminal_closed {administrative component : AuxiliaryComponent α Nat (Tagged β)}
    (same : Equivalent administrative (terminal (closed component))) :
    closed administrative = closed component := by
  have empty : administrative.core = .leaf := by
    have word := same.word
    cases core : administrative.core with
    | leaf => rfl
    | inner sz key value left right => simp [core,terminal] at word
  have marked : MarkedPorts administrative := same.marked (fun _ _ => closed_entry component)
  rw [closed_terminal administrative empty marked]
  change GapSource.encode (recordTree administrative.core) administrative.ports 0 = _
  rw [empty]
  exact same.ports 0 (by omega)

theorem wrap_invariant (component : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame (α := α) right))
    (clean : Clean component.core) (marked : MarkedPorts component) :
    Clean (PreferredContext.wrap component frames).core ∧
      MarkedPorts (PreferredContext.wrap component frames) := by
  induction frames generalizing component with
  | nil => exact ⟨clean,marked⟩
  | cons frame frames ih =>
      cases frame with
      | left record sibling outside cleanRecord direction represented =>
          exact ih _ (clean_append component clean _ _ cleanRecord _)
            (marked_append component marked _ _ _ (closed_entry outside))
      | right record sibling outside cleanRecord direction represented =>
          exact ih _ (clean_prepend _ _ cleanRecord _ component clean)
            (marked_prepend _ _ _ (closed_entry outside) component marked)

/-- One paid merge restores the ordinary preferred-path representation.
The supplied equality describes only the current seam's record word and
actual gap subtrees; the after-representation is proved here. -/
theorem merge_seam (source : Source α (Record (β := β)))
    (continuation administrative : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame (α := α) right))
    (represented : Represents right source continuation)
    (same : Equivalent administrative
      (PreferredContext.wrap (terminal (closed continuation)) frames))
    (allLeft : PreferredContext.before frames = [])
    (ordered : administrative.core.Ordered) (K : Nat)
    (height : (PreferredContext.plug source frames).shape.height ≤ K) :
    ∃ joined : AuxiliaryComponent α Nat (Tagged β),
      Represents right (PreferredContext.plug source frames) joined ∧
      Equivalent joined (PreferredContext.wrap continuation frames) ∧
      SourcePointer.Rearranges (closed administrative) (closed joined)
        (6720 * Nat.clog 2 (K + 1) + 90) := by
  have allRep := PreferredContext.represents frames represented
  have sizes := allRep.size_height.trans height
  have oldSize : administrative.core.size ≤ K := by
    rw [same.size,PreferredContext.size]
    rw [PreferredContext.size] at sizes
    change 0 + frames.length ≤ K
    omega
  have adminInvariant := wrap_invariant (terminal (closed continuation)) frames
    True.intro (fun _ _ => closed_entry continuation)
  have clean := same.clean adminInvariant.1
  have marked := same.marked adminInvariant.2
  cases boundary : PreferredContext.after frames with
  | nil =>
      have empty := empty_context (terminal (closed continuation)) frames allLeft boundary
      have physical := equivalent_terminal_closed (same.trans empty.symm)
      have joinedSame := empty_context continuation frames allLeft boundary
      exact ⟨continuation,allRep.equivalent joinedSame,joinedSame,by
        rw [physical]
        exact SourcePointer.rearranges_refl _ _⟩
  | cons pivot rest =>
      obtain ⟨found,cutSame,rejoin⟩ := prefix_context administrative (terminal (closed continuation))
        frames same ordered rest pivot allLeft boundary
      have joinedSame := rejoin continuation
      have joinedRep := allRep.equivalent joinedSame
      obtain ⟨continuationClean,continuationMarked⟩ := represented.invariant
      have repair : SourcePointer.Rearranges (closed (cutLeft administrative pivot.1 found))
          (closed continuation) 0 := by
        rw [equivalent_terminal_closed cutSame]
        exact SourcePointer.rearranges_refl _ _
      have cost := replacePrefix_charged administrative clean marked pivot.1 found continuation
        continuationClean continuationMarked 0 repair K oldSize
        (joinedRep.size_height.trans height)
      exact ⟨_,joinedRep,joinedSame,by simpa only [Nat.zero_add] using cost⟩

/-- The inverse operation produces the continuation actually extracted by
the balanced split. It preserves that continuation's representation and
puts its same closed physical tree in the administrative first gap. -/
theorem split_seam (source : Source α (Record (β := β)))
    (continuation joined : AuxiliaryComponent α Nat (Tagged β))
    (frames : List (ContextFrame (α := α) right))
    (represented : Represents right source continuation)
    (same : Equivalent joined (PreferredContext.wrap continuation frames))
    (allLeft : PreferredContext.before frames = [])
    (ordered : joined.core.Ordered) (K : Nat)
    (height : (PreferredContext.plug source frames).shape.height ≤ K) :
    ∃ actual administrative : AuxiliaryComponent α Nat (Tagged β),
      Represents right source actual ∧ Equivalent actual continuation ∧
      Equivalent administrative (PreferredContext.wrap (terminal (closed actual)) frames) ∧
      SourcePointer.Rearranges (closed joined) (closed administrative)
        (6720 * Nat.clog 2 (K + 1) + 90) := by
  have joinedRep := (PreferredContext.represents frames represented).equivalent same
  obtain ⟨clean,marked⟩ := joinedRep.invariant
  have oldSize := joinedRep.size_height.trans height
  cases boundary : PreferredContext.after frames with
  | nil =>
      have actualSame := same.trans (empty_context continuation frames allLeft boundary).symm
      have adminSame := empty_context (terminal (closed joined)) frames allLeft boundary
      refine ⟨joined,terminal (closed joined),represented.equivalent actualSame,actualSame,adminSame,?_⟩
      rw [terminal_closed]
      exact SourcePointer.rearranges_refl _ _
  | cons pivot rest =>
      obtain ⟨found,actualSame,rejoin⟩ :=
        prefix_context joined continuation frames same ordered rest pivot allLeft boundary
      let actual := cutLeft joined pivot.1 found
      let fresh := terminal (closed actual)
      have actualRep : Represents right source actual := represented.equivalent actualSame
      have adminSame := rejoin fresh
      have freshClean : Clean fresh.core := True.intro
      have freshMarked : MarkedPorts fresh := fun _ _ => closed_entry actual
      have repair : SourcePointer.Rearranges (closed actual) (closed fresh) 0 := by
        rw [terminal_closed]
        exact SourcePointer.rearranges_refl _ _
      have newSize : (replacePrefix joined pivot.1 found fresh).core.size ≤ K := by
        rw [adminSame.size,PreferredContext.size]
        have combined := (PreferredContext.represents frames represented).size_height.trans height
        rw [PreferredContext.size] at combined
        change 0 + frames.length ≤ K
        omega
      have cost := replacePrefix_charged joined clean marked pivot.1 found fresh
        freshClean freshMarked 0 repair K oldSize newSize
      exact ⟨actual,_,actualRep,actualSame,adminSame,by simpa only [Nat.zero_add] using cost⟩

end MultiSplay.ComparatorSeam
