import DynamicOptimality.SingleFinger.DequePop
import DynamicOptimality.SingleFinger.DequePopMax
import ChaCha.Paper20261030.SearchRotationMetadata

/-! Reusable deque endpoint operations in the shared rotation model.
The established local-controller routines are reused by adding temporary
proof-only records and then forgetting them. No metadata key remains in
the physical BST and no endpoint operation assumes a rotation bound. -/

namespace DynamicOptimality.MultiFinger.Deque

open ChaCha.MTR
open ChaCha.Paper20261030.Auxiliary
open DynamicOptimality.SingleFinger
open SearchRotation

abbrev Layout := SingleFinger.Deque.Layout
abbrev Record (α : Type*) := NodeRecord α (fun _ => Unit)

def annotate {α : Type*} : RawTree α → RawTree (Record α)
  | .empty => .empty
  | .node left key right => .node (annotate left) (0,⟨key,()⟩) (annotate right)

def annotateCell {α : Type*} (cell : Spine.Cell α) : Spine.Cell (Record α) :=
  ((0,⟨cell.1,()⟩),annotate cell.2)

def annotateLayout {α : Type*} (layout : Layout α) : Layout (Record α) :=
  ⟨annotate layout.gap,layout.front.map annotateCell,(0,⟨layout.pivot,()⟩),
    annotate layout.afterGap,layout.back.map annotateCell⟩

def forgetCell {α : Type*} (cell : Spine.Cell (Record α)) : Spine.Cell α :=
  (cell.1.2.1,Metadata.forgetTree cell.2)

def forgetLayout {α : Type*} (layout : Layout (Record α)) : Layout α :=
  ⟨Metadata.forgetTree layout.gap,layout.front.map forgetCell,layout.pivot.2.1,
    Metadata.forgetTree layout.afterGap,layout.back.map forgetCell⟩

@[simp] theorem forget_annotate {α : Type*} (tree : RawTree α) :
    Metadata.forgetTree (annotate tree) = tree := by induction tree <;> simp_all [annotate,Metadata.forgetTree]

@[simp] theorem forget_annotate_cell {α : Type*} (cell : Spine.Cell α) :
    forgetCell (annotateCell cell) = cell := by rcases cell with ⟨key,gap⟩; simp [forgetCell,annotateCell]

@[simp] theorem forget_annotate_layout {α : Type*} (layout : Layout α) :
    forgetLayout (annotateLayout layout) = layout := by
  cases layout
  simp [forgetLayout,annotateLayout,List.map_map,Function.comp_def]

@[simp] theorem forget_rightSpine {α : Type*} (gap : RawTree (Record α)) (cells : List (Spine.Cell (Record α))) :
    Metadata.forgetTree (Spine.rightSpine gap cells) =
      Spine.rightSpine (Metadata.forgetTree gap) (cells.map forgetCell) := by
  induction cells generalizing gap with
  | nil => rfl
  | cons cell cells ih => rcases cell with ⟨key,next⟩; simp [Spine.rightSpine,Metadata.forgetTree,forgetCell,ih]

@[simp] theorem forget_leftSpine {α : Type*} (gap : RawTree (Record α)) (cells : List (Spine.Cell (Record α))) :
    Metadata.forgetTree (Spine.leftSpine gap cells) =
      Spine.leftSpine (Metadata.forgetTree gap) (cells.map forgetCell) := by
  induction cells generalizing gap with
  | nil => rfl
  | cons cell cells ih => rcases cell with ⟨key,next⟩; simp [Spine.leftSpine,Metadata.forgetTree,forgetCell,ih]

@[simp] theorem forget_tree {α : Type*} (layout : Layout (Record α)) :
    Metadata.forgetTree layout.tree = (forgetLayout layout).tree := by
  simp [SingleFinger.Deque.Layout.tree,Metadata.forgetTree,forgetLayout]

@[simp] theorem forget_cells {α : Type*} (layout : Layout (Record α)) :
    (layout.cells.map forgetCell) = (forgetLayout layout).cells := by
  simp [SingleFinger.Deque.Layout.cells,forgetLayout,forgetCell]

@[simp] theorem forget_potential {α : Type*} (layout : Layout (Record α)) :
    (forgetLayout layout).potential = layout.potential := by
  simp [SingleFinger.Deque.Layout.potential,forgetLayout]

@[simp] theorem annotate_potential {α : Type*} (layout : Layout α) :
    (annotateLayout layout).potential = layout.potential := by
  simp [SingleFinger.Deque.Layout.potential,annotateLayout]

/-- The popped minimum becomes the actual parent of the remaining deque.
The bound uses the persistent imbalance potential of the actual layout. -/
 theorem pop_min {α : Type*} (layout : Layout α) (enough : 2 ≤ layout.cells.length) :
    ∃ (after : Layout α) (key : α) (rotations : Nat),
      layout.cells = (key,after.gap)::after.cells ∧
      Rotations layout.tree (.node layout.gap key after.tree) rotations ∧
      rotations+after.potential ≤ layout.potential+14 := by
  have enough' : 2 ≤ (annotateLayout layout).cells.length := by
    simpa [SingleFinger.Deque.Layout.cells,annotateLayout] using enough
  obtain ⟨after,key,cost,cells,program,amortized⟩ :=
    SingleFinger.Deque.pop_min (annotateLayout layout) enough' [] []
  obtain ⟨visits,trace⟩ := (program.run rfl).trace.forget
  obtain ⟨rotations,physical,bound⟩ := ChaCha.Paper20261030.SearchRotationBridge.pointer_trace_rotations trace
  have rawGap : Metadata.forgetTree (annotateLayout layout).gap = layout.gap := forget_annotate _
  have treeRun : Rotations layout.tree (.node layout.gap key.2.1 (forgetLayout after).tree) rotations := by
    simpa only [Metadata.forgetCursor,Metadata.forgetFrame,List.map_nil,List.map_cons,
      Pointer.Cursor.tree,Pointer.plug,forget_tree,forget_annotate_layout,rawGap] using physical
  have word := congrArg (List.map forgetCell) cells
  have word' : layout.cells = (key.2.1,(forgetLayout after).gap)::(forgetLayout after).cells := by
    change layout.cells = (key.2.1,Metadata.forgetTree after.gap)::(forgetLayout after).cells
    simpa only [List.map_cons,forget_cells,forget_annotate_layout,forgetCell] using word
  refine ⟨forgetLayout after,key.2.1,rotations,word',treeRun,?_⟩
  rw [forget_potential]
  rw [annotate_potential] at amortized
  omega

/-- Symmetric maximum exposure, retaining the final arbitrary gap subtree. -/
 theorem pop_max {α : Type*} (layout : Layout α) (enough : 2 ≤ layout.cells.length) :
    ∃ (after : Layout α) (key : α) (gap : RawTree α) (rotations : Nat),
      layout.cells = after.cells++[(key,gap)] ∧ after.gap = layout.gap ∧
      Rotations layout.tree (.node after.tree key gap) rotations ∧
      rotations+after.potential ≤ layout.potential+14 := by
  have enough' : 2 ≤ (annotateLayout layout).cells.length := by
    simpa [SingleFinger.Deque.Layout.cells,annotateLayout] using enough
  obtain ⟨after,key,gap,cost,cells,sameGap,program,amortized⟩ :=
    SingleFinger.Deque.pop_max (annotateLayout layout) enough' [] []
  obtain ⟨visits,trace⟩ := (program.run rfl).trace.forget
  obtain ⟨rotations,physical,bound⟩ := ChaCha.Paper20261030.SearchRotationBridge.pointer_trace_rotations trace
  have treeRun : Rotations layout.tree (.node (forgetLayout after).tree key.2.1 (Metadata.forgetTree gap)) rotations := by
    simpa only [Metadata.forgetCursor,Metadata.forgetFrame,List.map_nil,List.map_cons,
      Pointer.Cursor.tree,Pointer.plug,forget_tree,forget_annotate_layout] using physical
  have word := congrArg (List.map forgetCell) cells
  have word' : layout.cells = (forgetLayout after).cells++[(key.2.1,Metadata.forgetTree gap)] := by
    simpa only [List.map_append,List.map_cons,List.map_nil,forget_cells,forget_annotate_layout,forgetCell] using word
  refine ⟨forgetLayout after,key.2.1,Metadata.forgetTree gap,rotations,word',?_,treeRun,?_⟩
  · change Metadata.forgetTree after.gap = layout.gap
    rw [sameGap]
    exact forget_annotate layout.gap
  · rw [forget_potential]
    rw [annotate_potential] at amortized
    omega

 theorem push_min {α : Type*} (layout : Layout α) (key : α) (gap : RawTree α) :
    Rotations (.node gap key layout.tree) (SingleFinger.Deque.pushMinLayout layout key gap).tree 1 ∧
      1+(SingleFinger.Deque.pushMinLayout layout key gap).potential ≤ layout.potential+5 := by
  exact ⟨.singleton (.rootLeft _ _ _ _ _),SingleFinger.Deque.push_min_amortized layout key gap⟩

 theorem push_max {α : Type*} (layout : Layout α) (key : α) (gap : RawTree α) :
    Rotations (.node layout.tree key gap) (SingleFinger.Deque.pushMaxLayout layout key gap).tree 1 ∧
      1+(SingleFinger.Deque.pushMaxLayout layout key gap).potential ≤ layout.potential+5 := by
  refine ⟨?_,SingleFinger.Deque.push_max_amortized layout key gap⟩
  have step : Rotation (.node layout.tree key gap)
      (.node (Spine.rightSpine layout.gap layout.front) layout.pivot
        (.node (Spine.leftSpine layout.afterGap layout.back) key gap)) := .rootRight _ _ _ _ _
  simpa only [SingleFinger.Deque.pushMaxLayout,SingleFinger.Deque.Layout.tree,
    Spine.leftSpine_append,Spine.leftSpine] using Rotations.singleton step

end DynamicOptimality.MultiFinger.Deque
