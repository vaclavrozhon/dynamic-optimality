import TangoSquared.Paper20261030.SourceReversal

/-! An actual source execution that reaches and reads a specified leaf.
The witness splits the trace at the reached physical leaf, and returns
to the root in the same outside ancestor context. This is a source-tree
service notion, not yet an ordinary original-key BST access. -/

namespace TangoSquared.Paper20261030.SourcePointer

open ColoredStorage

variable {α ρ : Type*}

def VisitsLeaf (key : α) (before after : Source α ρ) (budget : Nat) : Prop :=
  ∀ ancestors : List (Frame α ρ), ∃ (atLeaf : Cursor α ρ) (record : ρ)
    (firstReads lastReads : List ρ) (firstCost lastCost : Nat),
    Trace ⟨before,ancestors⟩ firstReads atLeaf firstCost ∧
    atLeaf.focus = .leaf key record ∧
    Trace atLeaf (record :: lastReads) ⟨after,ancestors⟩ lastCost ∧
    firstCost + lastCost ≤ budget

theorem VisitsLeaf.mono {key : α} {before after : Source α ρ} {m n : Nat}
    (h : VisitsLeaf key before after m) (hmn : m ≤ n) : VisitsLeaf key before after n := by
  intro ancestors
  obtain ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,first,focus,last,bound⟩ := h ancestors
  exact ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,first,focus,last,bound.trans hmn⟩

theorem VisitsLeaf.prepend {key : α} {a b c : Source α ρ} {m n : Nat}
    (h : Rearranges a b m) (v : VisitsLeaf key b c n) : VisitsLeaf key a c (m + n) := by
  intro ancestors
  obtain ⟨reads,cost,trace,bound⟩ := h ancestors
  obtain ⟨atLeaf,record,firstReads,lastReads,firstCost,lastCost,first,focus,last,visitBound⟩ := v ancestors
  exact ⟨atLeaf,record,reads ++ firstReads,lastReads,cost + firstCost,lastCost,
    trace.append first,focus,last,by omega⟩

end TangoSquared.Paper20261030.SourcePointer
