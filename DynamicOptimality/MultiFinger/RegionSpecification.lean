import DynamicOptimality.MultiFinger.TopAccess

/-! # Specification of a bounded consecutive-marker replacement

A region consists of consecutive top-tree markers and all the gaps
between and immediately beside them. The aligned prefix and suffix
record the unchanged markers and physical gaps outside that region.
Neither the containing top tree nor the region has a prescribed shape.

The proposition below is an interface for a theorem to be proved from
ordinary splay, marker promotion, and marker demotion. Defining this
interface does not assert that such a simulator exists.
-/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open ChaCha.Paper20261030.SplayAuxiliary (potential)

structure RegionFrame (α : Type*) where
  beforeKeys : List α
  afterKeys : List α
  beforeHoles : List (RawTree α)
  afterHoles : List (RawTree α)
  beforeCount : beforeHoles.length = beforeKeys.length
  afterCount : afterHoles.length = afterKeys.length

def RegionFrame.Contains {α : Type*} (frame : RegionFrame α)
    (whole block : MarkedTree α) : Prop :=
  whole.skeleton.inorder =
    frame.beforeKeys ++ block.skeleton.inorder ++ frame.afterKeys ∧
  whole.holes = frame.beforeHoles ++ block.holes ++ frame.afterHoles

/-- Replace at most three consecutive retained markers by at most three
new retained markers. The physical region is transformed by the supplied
actual rotation trace; only the logarithmic top-tree overhead is new.
The capacity allows three temporary promotions during replacement.

This is deliberately a specification, not an assumed theorem or a
public competitive endpoint. -/
def RegionReplacementBound (constant : Nat) : Prop :=
  ∀ (frame : RegionFrame Nat) (before oldBlock newBlock : MarkedTree Nat)
    (rawCount capacity : Nat),
    frame.Contains before oldBlock →
    before.erase.Ordered →
    (frame.beforeKeys ++ newBlock.skeleton.inorder ++ frame.afterKeys).Nodup →
    before.skeleton.size ≤ capacity →
    oldBlock.skeleton.size ≤ 3 →
    newBlock.skeleton.size ≤ 3 →
    SearchRotation.Rotations oldBlock.erase newBlock.erase rawCount →
    ∃ after : MarkedTree Nat, ∃ count : Nat,
      frame.Contains after newBlock ∧
      SearchRotation.Rotations before.erase after.erase count ∧
      count + 2 * potential after.skeleton ≤
        2 * potential before.skeleton + rawCount +
        constant * (1 + Nat.log 2 (capacity + 4))

end DynamicOptimality.MultiFinger
