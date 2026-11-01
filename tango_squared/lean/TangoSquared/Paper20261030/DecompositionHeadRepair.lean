import TangoSquared.Paper20261030.PathDecomposition
import TangoSquared.Paper20261030.ComponentPreferenceFlip
import TangoSquared.Paper20261030.EndpointObservations

/-!
# A physical head repair preserves the reference decomposition

The represented old path identifies the head as its extreme separator.
After exposing that separator, its old continuation is equivalent to the
represented child component, even though its balancing shape changed.
The incoming component is already in the identified physical extreme
port. The charged preference flip therefore represents exactly the
reference fork with its updated preference payload, and retains both
children's reference states.
-/

namespace TangoSquared.Paper20261030.PathDecomposition

open Std Std.DTreeMap.Internal Std.DTreeMap.Internal.Impl
open ColoredStorage Auxiliary Auxiliary.Metadata AuxiliaryComponent BoundaryObservations

variable {α : Type*} {β : Nat → Type*}

theorem left_head_repair (right : Record (β := β) → Bool)
    (record : Record (β := β)) (l r : Source α (Record (β := β)))
    (lc rc c : AuxiliaryComponent α Nat (Tagged β))
    (hl : Represents right l lc) (hr : Represents right r rc)
    (same : Equivalent c (append lc record.2.1 record.2.2 (closed rc)))
    (oldDirection : right record = false) (oldClean : entry record = false) (ordered : c.core.Ordered)
    (fresh : Tagged β record.2.1) (freshClean : fresh.2 = false)
    (newDirection : right (record.1,⟨record.2.1,fresh⟩) = true) :
    ∃ d : AuxiliaryComponent α Nat (Tagged β),
      Represents right (.fork (record.1,⟨record.2.1,fresh⟩) l r) d ∧
      SourcePointer.Rearranges (closed c) (closed d)
        (5730 * Nat.clog 2 (c.core.size + 1) + 495 * Nat.clog 2 (rc.core.size + 1) + 90) := by
  have endpoint : extreme true c.core = some record.2 := by
    rw [extreme_last,same.word,append_word]
    simp
  let found := extreme_found true c.core ordered endpoint
  have empty := maximum_split_empty c.core c.balanced ordered endpoint
  have old : Represents right (.fork record l r) c := .left oldDirection oldClean hl hr same
  obtain ⟨hc,hp⟩ := old.invariant
  obtain ⟨hrc,hrp⟩ := hr.invariant
  have recovered := max_left_equivalent c lc record.2.1 record.2.2 (closed rc) same found empty
  have representedLeft := hl.equivalent recovered
  have attached : c.ports c.core.size = closed rc := by
    rw [same.ports _ le_rfl,same.size,append_size]
    simp only [append,show ¬ lc.core.size + 1 ≤ lc.core.size by omega,if_false]
  let d := preferRight c rc record.2.1 found fresh
  have represented : Represents right (.fork (record.1,⟨record.2.1,fresh⟩) l r) d :=
    .right newDirection freshClean representedLeft hr (.refl _)
  exact ⟨d,represented,preferRight_charged c rc hc hrc hp hrp record.2.1 found empty attached fresh⟩

theorem right_head_repair (right : Record (β := β) → Bool)
    (record : Record (β := β)) (l r : Source α (Record (β := β)))
    (lc rc c : AuxiliaryComponent α Nat (Tagged β))
    (hl : Represents right l lc) (hr : Represents right r rc)
    (same : Equivalent c (prepend record.2.1 record.2.2 (closed lc) rc))
    (oldDirection : right record = true) (oldClean : entry record = false) (ordered : c.core.Ordered)
    (fresh : Tagged β record.2.1) (freshClean : fresh.2 = false)
    (newDirection : right (record.1,⟨record.2.1,fresh⟩) = false) :
    ∃ d : AuxiliaryComponent α Nat (Tagged β),
      Represents right (.fork (record.1,⟨record.2.1,fresh⟩) l r) d ∧
      SourcePointer.Rearranges (closed c) (closed d)
        (5730 * Nat.clog 2 (c.core.size + 1) + 495 * Nat.clog 2 (lc.core.size + 1) + 90) := by
  have endpoint : extreme false c.core = some record.2 := by
    rw [extreme_first,same.word,prepend_word]
    rfl
  let found := extreme_found false c.core ordered endpoint
  have empty := minimum_split_empty c.core c.balanced ordered endpoint
  have old : Represents right (.fork record l r) c := .right oldDirection oldClean hl hr same
  obtain ⟨hc,hp⟩ := old.invariant
  obtain ⟨hlc,hlp⟩ := hl.invariant
  have recovered := min_right_equivalent c rc record.2.1 record.2.2 (closed lc) same found empty
  have representedRight := hr.equivalent recovered
  have attached : c.ports 0 = closed lc := by
    rw [same.ports 0 (Nat.zero_le _)]
    simp only [prepend,if_true]
  let d := preferLeft lc c record.2.1 found fresh
  have represented : Represents right (.fork (record.1,⟨record.2.1,fresh⟩) l r) d :=
    .left newDirection freshClean hl representedRight (.refl _)
  exact ⟨d,represented,preferLeft_charged lc c hlc hc hlp hp record.2.1 found empty attached fresh⟩

end TangoSquared.Paper20261030.PathDecomposition
