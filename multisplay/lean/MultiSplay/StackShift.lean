import MultiSplay.OrdinalShift

/-!
# Persistent stacks under a change of ordinal origin

All four stack transports retain the virtual template, digits, and shaping
witness. Only the physical substitution changes. Consequently the potential is
identical, including for a stack reached after an arbitrary prior history.
-/

namespace MultiSplay.OrdinalShift

open Splay.Accounting.OfflineConnectedSupport (SupportFrontier)
open Splay.Accounting.OfflineNormalForm.RibStack

/-- The explicit target frontier avoids casting the stack's physical tree. -/
def minimumTo (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : MinimumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) : MinimumStack capacity target where
  virtualLower := stack.virtualLower
  template := stack.template
  digits := stack.digits
  shaped := stack.shaped
  tree := tree offset stack.tree
  filling := substitution offset stack.filling
  frontier_eq := by rw [substitution_selected, selected_frontier, stack.frontier_eq]; exact same

def maximumTo (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : MaximumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) : MaximumStack capacity target where
  virtualLower := stack.virtualLower
  template := stack.template
  digits := stack.digits
  shaped := stack.shaped
  imageUpper := stack.imageUpper
  image := stack.image
  reflection := stack.reflection
  tree := tree offset stack.tree
  filling := substitution offset stack.filling
  frontier_eq := by rw [substitution_selected, selected_frontier, stack.frontier_eq]; exact same

def foldedMinimumTo (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : FoldedMinimumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) : FoldedMinimumStack capacity target where
  virtualLower := stack.virtualLower
  template := stack.template
  digits := stack.digits
  shaped := stack.shaped
  tree := tree offset stack.tree
  filling := substitution offset stack.filling
  frontier_eq := by rw [substitution_selected, selected_frontier, stack.frontier_eq]; exact same

def foldedMaximumTo (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : FoldedMaximumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) : FoldedMaximumStack capacity target where
  virtualLower := stack.virtualLower
  template := stack.template
  digits := stack.digits
  shaped := stack.shaped
  imageUpper := stack.imageUpper
  image := stack.image
  reflection := stack.reflection
  tree := tree offset stack.tree
  filling := substitution offset stack.filling
  frontier_eq := by rw [substitution_selected, selected_frontier, stack.frontier_eq]; exact same

@[simp] theorem minimumTo_potential (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : MinimumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) :
    (minimumTo offset stack same).potential = stack.potential := rfl

@[simp] theorem maximumTo_potential (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : MaximumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) :
    (maximumTo offset stack same).potential = stack.potential := rfl

@[simp] theorem foldedMinimumTo_potential (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : FoldedMinimumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) :
    (foldedMinimumTo offset stack same).potential = stack.potential := rfl

@[simp] theorem foldedMaximumTo_potential (offset : Nat) {capacity lower upper : Nat}
    {source : SupportFrontier lower upper} (stack : FoldedMaximumStack capacity source)
    {target : SupportFrontier (offset + lower) (offset + upper)}
    (same : frontier offset source = target) :
    (foldedMaximumTo offset stack same).potential = stack.potential := rfl

end MultiSplay.OrdinalShift
