import ChaCha.Paper20261030.PackedCursorRotation

/-!
# Complete traces for one represented source cursor

For a fixed color present in the component, every source trace has an
actual trace in the packed record tree, ending at its represented active
or parked cursor and costing at most seventeen times as much. Physical
reads return the lists at the vertices that are actually reached.

This is the one-cursor trace correspondence. The local rotation kernels
still take the pivot values as inputs. Structural fields, acquisition of
those inputs, simultaneous cursors, and the component header belong to
the remaining full simulation proof.
-/

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer

variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

theorem represented_step (color : α → C) (q : C)
    {source final : Cursor α ρ} (step : SourcePointer.Step source final)
    {physical : Cursor α (List ρ)} (h : Represents color q source physical) :
    ∃ (actual : Cursor α (List ρ)) (reads : List (List ρ)) (cost : Nat),
      SourcePointer.Trace physical reads actual cost ∧ cost ≤ 17 ∧
      Represents color q final actual := by
  cases step with
  | left l r record rest =>
    obtain ⟨actual,cost,trace,hcost,represented⟩ := navigation color q h (.left l r record rest)
    exact ⟨actual,[],cost,trace,by omega,represented⟩
  | right l r record rest =>
    obtain ⟨actual,cost,trace,hcost,represented⟩ := navigation color q h (.right l r record rest)
    exact ⟨actual,[],cost,trace,by omega,represented⟩
  | upLeft l r record rest =>
    obtain ⟨actual,cost,trace,hcost,represented⟩ := navigation color q h (.upLeft l r record rest)
    exact ⟨actual,[],cost,trace,by omega,represented⟩
  | upRight l r record rest =>
    obtain ⟨actual,cost,trace,hcost,represented⟩ := navigation color q h (.upRight l r record rest)
    exact ⟨actual,[],cost,trace,by omega,represented⟩
  | rotateRight u v w p r rest => exact rotate_right color q u v w p r rest h
  | rotateLeft u v w p r rest => exact rotate_left color q u v w p r rest h
  | write focus fresh rest =>
    by_cases hq : q = focus.rootOwner color
    · subst q
      obtain ⟨actual,trace,represented⟩ := write_record color ⟨focus,rest⟩ fresh h
      exact ⟨actual,_,2,trace,by decide,represented⟩
    · exact ⟨physical,[],0,.nil _,by decide,write_other color q ⟨focus,rest⟩ fresh hq h⟩

theorem represented_trace (color : α → C) (q : C)
    {source final : Cursor α ρ} {observations : List ρ} {sourceCost : Nat}
    (execution : SourcePointer.Trace source observations final sourceCost)
    {physical : Cursor α (List ρ)} (h : Represents color q source physical) :
    ∃ (actual : Cursor α (List ρ)) (reads : List (List ρ)) (cost : Nat),
      SourcePointer.Trace physical reads actual cost ∧ cost ≤ 17 * sourceCost ∧
      Represents color q final actual := by
  induction execution generalizing physical with
  | nil source => exact ⟨physical,[],0,.nil _,Nat.zero_le _,h⟩
  | step move rest ih =>
    obtain ⟨middle,firstReads,firstCost,firstTrace,hfirst,hmiddle⟩ := represented_step color q move h
    obtain ⟨actual,lastReads,lastCost,lastTrace,hlast,hactual⟩ := ih hmiddle
    exact ⟨actual,_,_,firstTrace.append lastTrace,by omega,hactual⟩
  | read rest ih =>
    obtain ⟨actual,reads,cost,trace,hcost,hactual⟩ := ih h
    exact ⟨actual,_,_,.read trace,by omega,hactual⟩

end ChaCha.Paper20261030.ColoredStorage
