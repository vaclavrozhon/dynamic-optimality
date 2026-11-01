import TangoSquared.Paper20261030.DecoratedContextReassembly
import TangoSquared.Paper20261030.PackedRotation

/-!
# Reassembly of the actual colored record packing around fixed blocks

Substitute whole source blocks into an exposed binary context. Its packed
color restriction is exactly a decorated context on the packed blocks:
each connector record is placed at the root selected by the existing
owner rule. The general charged reassembly therefore transforms the
actual old packing into the actual new packing, including suppressed
connector records, without changing any block interior.
-/

namespace TangoSquared.Paper20261030.ProjectionLocal

open ColoredStorage

variable {α ρ : Type*}

theorem decorate_nil (t : Projected α ρ) : decorate [] t = t := by
  cases t with
  | none => rfl
  | some t => cases t <;> rfl

theorem attach_as_decorate (present : Bool) (record : ρ) (t : Projected α ρ) :
    attach present record t = decorate (if present then [record] else []) t := by
  cases present
  · exact (decorate_nil t).symm
  · rfl

end TangoSquared.Paper20261030.ProjectionLocal

namespace TangoSquared.Paper20261030.OrderedContext

open ColoredStorage ProjectionLocal

variable {ι α ρ C : Type*}

def substituteSource (blocks : ι → Source α ρ) : Source ι ρ → Source α ρ
  | .leaf key _ => blocks key
  | .fork record l r => .fork record (substituteSource blocks l) (substituteSource blocks r)

def packedContext [LinearOrder C] (color : α → C) (q : C) (blocks : ι → Source α ρ) :
    Source ι ρ → Source ι (List ρ)
  | .leaf key _ => .leaf key []
  | .fork record l r =>
      .fork (if owner color (substituteSource blocks l) (substituteSource blocks r) = q then [record] else [])
        (packedContext color q blocks l) (packedContext color q blocks r)

theorem packedContext_shape [LinearOrder C] (color : α → C) (q : C)
    (blocks : ι → Source α ρ) (t : Source ι ρ) :
    (packedContext color q blocks t).shape = t.shape := by
  induction t <;> simp_all [packedContext,Source.shape]

theorem packed_substitution [LinearOrder C] (color : α → C) (q : C)
    (blocks : ι → Source α ρ) (t : Source ι ρ) :
    packed color q (substituteSource blocks t) =
      decorated (fun key => packed color q (blocks key)) (packedContext color q blocks t) := by
  induction t with
  | leaf key record =>
    simp only [substituteSource,packedContext,decorated,decorate_nil]
  | fork record l r ihl ihr =>
    simp only [substituteSource,packed_fork,attach_as_decorate,decide_eq_true_eq,
      packedContext,decorated,ihl,ihr]

theorem packed_reassembly [LinearOrder C] (color : α → C) (q : C)
    (blocks : ι → Source α ρ) (before after : Source ι ρ)
    (orderedBlocks : before.shape.leaves = after.shape.leaves) (k : Nat)
    (beforeSize : before.shape.leaves.length = k) :
    Rearranges (packed color q (substituteSource blocks before))
      (packed color q (substituteSource blocks after)) (36 * k) := by
  rw [packed_substitution,packed_substitution]
  apply reassemble_decorated
  · simpa only [packedContext_shape] using orderedBlocks
  · simpa only [packedContext_shape] using beforeSize

end TangoSquared.Paper20261030.OrderedContext
