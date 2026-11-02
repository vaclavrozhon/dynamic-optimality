import DynamicOptimality.MultiFinger.MarkedTendon
import DynamicOptimality.MultiFinger.RegionSpecification

/-! Exact marker and opaque-gap words of open tendon ports.
A right-open port is a prefix of those words, and a left-open port is a
suffix. These identities permit moving a whole half-tendon through an
arbitrary top-splay shape without copying or changing its hanging trees. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open DynamicOptimality.GeometricOnlineSimulation
open TendonContents

variable {α : Type*}

def rightKeys (port : RightPort α) : List α :=
  [port.pivot] ++ port.middle.toList.map Prod.snd

def rightHoles (port : RightPort α) : List (RawTree α) :=
  [port.left] ++ port.middle.toList.map Prod.fst

def leftKeys (port : LeftPort α) : List α :=
  port.middle.toList.map Prod.fst ++ [port.pivot]

def leftHoles (port : LeftPort α) : List (RawTree α) :=
  port.middle.toList.map Prod.snd ++ [port.right]

def lowKeys (queue : Option (OpenDeque.Right α)) : List α :=
  (queue.map (fun layout => rightKeys layout.port)).getD []

def lowHoles (queue : Option (OpenDeque.Right α)) : List (RawTree α) :=
  (queue.map (fun layout => rightHoles layout.port)).getD []

def highKeys (queue : Option (OpenDeque.Left α)) : List α :=
  (queue.map (fun layout => leftKeys layout.port)).getD []

def highHoles (queue : Option (OpenDeque.Left α)) : List (RawTree α) :=
  (queue.map (fun layout => leftHoles layout.port)).getD []

theorem low_count (queue : Option (OpenDeque.Right α)) :
    (lowHoles queue).length = (lowKeys queue).length := by
  cases queue <;> simp [lowHoles,lowKeys,rightHoles,rightKeys]

theorem high_count (queue : Option (OpenDeque.Left α)) :
    (highHoles queue).length = (highKeys queue).length := by
  cases queue <;> simp [highHoles,highKeys,leftHoles,leftKeys]

theorem rightMarked_word (port : RightPort α) (inside : MarkedTree α) :
    (rightMarked port inside).skeleton.inorder = rightKeys port ++ inside.skeleton.inorder := by
  cases shape : port.middle <;>
    simp [rightMarked,rightKeys,shape,MarkedTree.skeleton,Tree.inorder,List.append_assoc]

theorem rightMarked_holes (port : RightPort α) (inside : MarkedTree α) :
    (rightMarked port inside).holes = rightHoles port ++ inside.holes := by
  cases shape : port.middle <;> simp [rightMarked,rightHoles,shape,MarkedTree.holes,List.append_assoc]

theorem leftMarked_word (port : LeftPort α) (inside : MarkedTree α) :
    (leftMarked port inside).skeleton.inorder = inside.skeleton.inorder ++ leftKeys port := by
  cases shape : port.middle <;>
    simp [leftMarked,leftKeys,shape,MarkedTree.skeleton,Tree.inorder,List.append_assoc]

theorem leftMarked_holes (port : LeftPort α) (inside : MarkedTree α) :
    (leftMarked port inside).holes = inside.holes ++ leftHoles port := by
  cases shape : port.middle <;> simp [leftMarked,leftHoles,shape,MarkedTree.holes,List.append_assoc]

theorem lowMarked_word (queue : Option (OpenDeque.Right α)) (inside : MarkedTree α) :
    (lowMarked queue inside).skeleton.inorder = lowKeys queue ++ inside.skeleton.inorder := by
  cases queue with
  | none => rfl
  | some layout => exact rightMarked_word layout.port inside

theorem lowMarked_holes (queue : Option (OpenDeque.Right α)) (inside : MarkedTree α) :
    (lowMarked queue inside).holes = lowHoles queue ++ inside.holes := by
  cases queue with
  | none => rfl
  | some layout => exact rightMarked_holes layout.port inside

theorem highMarked_word (queue : Option (OpenDeque.Left α)) (inside : MarkedTree α) :
    (highMarked queue inside).skeleton.inorder = inside.skeleton.inorder ++ highKeys queue := by
  cases queue with
  | none => simp [highMarked,highKeys]
  | some layout => exact leftMarked_word layout.port inside

theorem highMarked_holes (queue : Option (OpenDeque.Left α)) (inside : MarkedTree α) :
    (highMarked queue inside).holes = inside.holes ++ highHoles queue := by
  cases queue with
  | none => simp [highMarked,highHoles]
  | some layout => exact leftMarked_holes layout.port inside

def firstHole : MarkedTree α → RawTree α
  | .hole tree => tree
  | .node left _ _ => firstHole left

def lastHole : MarkedTree α → RawTree α
  | .hole tree => tree
  | .node _ _ right => lastHole right

theorem firstHole_holes (tree : MarkedTree α) :
    tree.holes = firstHole tree :: tree.holes.tail := by
  induction tree with
  | hole => rfl
  | node left key right leftIH rightIH =>
      change left.holes++right.holes = firstHole left::(left.holes++right.holes).tail
      rw [leftIH]
      rfl

theorem lastHole_holes (tree : MarkedTree α) :
    tree.holes = tree.holes.dropLast++[lastHole tree] := by
  induction tree with
  | hole => rfl
  | node left key right leftIH rightIH =>
      change left.holes++right.holes = (left.holes++right.holes).dropLast++[lastHole right]
      rw [rightIH]
      simp only [← List.append_assoc,List.dropLast_concat]

theorem firstHole_length (tree : MarkedTree α) :
    tree.holes.tail.length = tree.skeleton.inorder.length := by
  have lengths := congrArg List.length (firstHole_holes tree)
  rw [MarkedTree.holes_length] at lengths
  rw [Tree.length_inorder]
  simp only [List.length_cons] at lengths
  omega

theorem lastHole_length (tree : MarkedTree α) :
    tree.holes.dropLast.length = tree.skeleton.inorder.length := by
  have lengths := congrArg List.length (lastHole_holes tree)
  rw [MarkedTree.holes_length] at lengths
  rw [Tree.length_inorder]
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

def DataEquivalent (before after : MarkedTree α) : Prop :=
  before.skeleton.inorder = after.skeleton.inorder ∧ before.holes = after.holes

@[refl] theorem DataEquivalent.refl (tree : MarkedTree α) : DataEquivalent tree tree := ⟨rfl,rfl⟩

theorem DataEquivalent.symm {before after : MarkedTree α} (same : DataEquivalent before after) :
    DataEquivalent after before := ⟨same.1.symm,same.2.symm⟩

theorem DataEquivalent.trans {first middle last : MarkedTree α}
    (a : DataEquivalent first middle) (b : DataEquivalent middle last) : DataEquivalent first last :=
  ⟨a.1.trans b.1,a.2.trans b.2⟩

end DynamicOptimality.MultiFinger
