import TangoSquared.Paper20261030.PackedExecution
import TangoSquared.Paper20261030.PreparedBlockIntervals
import TangoSquared.Paper20261030.SourceMirror

/-!
# Root-to-root cost correspondence for packed source operations

Any actual source rearrangement induces a root-to-root trace in each
fixed color projection with factor seventeen, including its packed
records. This specializes the maintained-cursor simulation to complete
auxiliary operations, including colors absent from the component.
Mirroring a projection preserves the bound.

This is a trace correspondence. Running the color cursors in lockstep,
the virtual header, bounded local control, and compilation into one
ordinary BST cursor remain obligations of the full implementation.
-/

namespace TangoSquared.Paper20261030.ColoredStorage

open SourcePointer RouterProjection

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem Source.support_leaves (color : α → C) (t : Source α ρ) :
    t.support color = (t.shape.leaves.map color).toFinset := by
  induction t <;> simp_all [support,Source.shape,Router.leaves,List.map_append,List.toFinset_append]

theorem packed_rearranges (color : α → C) (q : C) {before after : Source α ρ} {budget : Nat}
    (execution : SourcePointer.Rearranges before after budget) :
    ProjectionLocal.Rearranges (packed color q before) (packed color q after) (17 * budget) := by
  have support : before.support color = after.support color := by
    rw [Source.support_leaves,Source.support_leaves,execution.leaves]
  cases hb : packed color q before with
  | none =>
    have ha : packed color q after = none :=
      (packed_none_iff color q after).mpr (support ▸ (packed_none_iff color q before).mp hb)
    rw [ha]
    trivial
  | some initial =>
    have present : q ∈ before.support color := by
      by_contra absent
      have hn := (packed_none_iff color q before).mpr absent
      rw [hb] at hn
      contradiction
    obtain ⟨final,ha⟩ := packed_exists color q after (support ▸ present)
    rw [ha]
    intro ancestors
    obtain ⟨sourceReads,sourceCost,sourceTrace,sourceBound⟩ := execution []
    obtain ⟨actual,reads,cost,trace,bound,represented⟩ := represented_trace color q sourceTrace
      (represents_root color q before hb)
    have rooted := Represents.unique color q ⟨after,[]⟩ represented (represents_root color q after ha)
    rw [rooted] at trace
    refine ⟨reads,cost,?_,bound.trans (Nat.mul_le_mul_left 17 sourceBound)⟩
    exact trace.extend ancestors

end TangoSquared.Paper20261030.ColoredStorage

namespace TangoSquared.Paper20261030.ProjectionLocal

open ColoredStorage

variable {α ρ : Type*}

def mirror (t : Projected α ρ) : Projected α ρ := t.map Source.mirror

theorem Rearranges.mirror {before after : Projected α ρ} {budget : Nat}
    (execution : Rearranges before after budget) : Rearranges (mirror before) (mirror after) budget := by
  cases before <;> cases after
  · trivial
  · exact False.elim execution
  · exact False.elim execution
  · exact SourcePointer.Rearranges.mirror execution

end TangoSquared.Paper20261030.ProjectionLocal
