import ChaCha.Paper20261030.SplayAuxiliaryPotential
import ChaCha.Paper20261030.PathPorts
import ChaCha.Paper20261030.ProjectionLocal

/-!
# Actual splay traces with the original leaf-oriented payloads

An auxiliary separator tree has one payload in each inorder gap. These
payloads move intact under its ordinary splay rotations. The lemma below
lifts the existing single-cursor splay implementation, including its
initial descent, to the source model used by the colored physical compiler.
-/

namespace ChaCha.Paper20261030.SplayAuxiliary

open DynamicOptimality (RawTree)
open ChaCha.MTR
open ColoredStorage
open MultiSplay.Auxiliary

variable {α ρ : Type*}

theorem lift_pointer_trace {before after : Pointer.Cursor ρ} {reads : List ρ} {cost : Nat}
    (trace : Pointer.Trace before reads after cost)
    (ports : Nat → Source α ρ) (base : Nat) :
    SourcePointer.Trace (GapSource.cursor ports base before) reads
      (GapSource.cursor ports base after) cost := by
  induction trace with
  | nil => exact .nil _
  | step move remaining ih => exact .step (GapSource.nav move ports base) ih
  | @serve current final key reads cost found remaining ih =>
      have record : (GapSource.cursor ports base current).focus.rootRecord = key := by
        rcases current with ⟨tree,ancestors⟩
        cases tree with
        | empty => simp [Tree.rootKey] at found
        | node left root right =>
            exact Option.some.inj found
      simpa only [record] using SourcePointer.Trace.read ih

/-- A source trace with exact cost and untouched payload interiors. -/
theorem splay_source_trace {before after : RawTree ρ} {key : ρ} {rotations : Nat}
    (execution : Splay key before after rotations) (unique : before.inorder.Nodup)
    (ports : Nat → Source α ρ) (outside : List (SourcePointer.Frame α ρ)) :
    SourcePointer.Trace ⟨GapSource.encode before ports 0,outside⟩ [key]
      ⟨GapSource.encode after ports 0,outside⟩ (3*rotations+1) := by
  have trace := lift_pointer_trace (execution.pointer unique []) ports 0
  have rootTrace : SourcePointer.Trace ⟨GapSource.encode before ports 0,[]⟩ [key]
      ⟨GapSource.encode after ports 0,[]⟩ (3*rotations+1) := by
    simpa only [GapSource.cursor,GapSource.frames,PointerGraft.offset,Nat.add_zero] using trace
  simpa only [SourcePointer.Cursor.extend,List.nil_append] using rootTrace.extend outside

theorem splay_source_rearranges {before after : RawTree ρ} {key : ρ} {rotations : Nat}
    (execution : Splay key before after rotations) (unique : before.inorder.Nodup)
    (ports : Nat → Source α ρ) :
    SourcePointer.Rearranges (GapSource.encode before ports 0) (GapSource.encode after ports 0)
      (3*rotations+1) :=
  fun outside => ⟨[key],3*rotations+1,splay_source_trace execution unique ports outside,le_rfl⟩

/-- Existence, legality, and amortized cost refer to the same actual splay. -/
theorem splay_source_exists (before : RawTree ρ) (key : ρ) (present : key ∈ before.inorder)
    (unique : before.inorder.Nodup) (ports : Nat → Source α ρ) (capacity : Nat)
    (bounded : before.size ≤ capacity) :
    ∃ after rotations,
      Splay key before after rotations ∧
      SourcePointer.Rearranges (GapSource.encode before ports 0) (GapSource.encode after ports 0)
        (3*rotations+1) ∧
      (3*rotations+1)+6*potential after ≤ 6*potential before+18*Nat.log 2 capacity+4 := by
  classical
  obtain ⟨after,rotations,execution,physical⟩ := exists_pointer_splay present
  have amortized := splay_amortized_capacity execution unique bounded
  exact ⟨after,rotations,execution,splay_source_rearranges execution unique ports,by omega⟩

end ChaCha.Paper20261030.SplayAuxiliary
