import DynamicOptimality.MultiFinger.TendonInitialization

/-! A tendon exposes at most four real separator keys to the top tree.
Its arbitrary hanging subtrees remain holes; every retained child-hand
vertex is marked recursively. These are ordinary keys of the same BST. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open DynamicOptimality.GeometricOnlineSimulation
open TendonContents

variable {α : Type*}

def rightMarked (port : RightPort α) (inside : MarkedTree α) : MarkedTree α :=
  match port.middle with
  | none => .node (.hole port.left) port.pivot inside
  | some (middle,key) => .node (.hole port.left) port.pivot (.node (.hole middle) key inside)

def leftMarked (port : LeftPort α) (inside : MarkedTree α) : MarkedTree α :=
  match port.middle with
  | none => .node inside port.pivot (.hole port.right)
  | some (key,middle) => .node (.node inside key (.hole middle)) port.pivot (.hole port.right)

@[simp] theorem rightMarked_erase (port : RightPort α) (inside : MarkedTree α) :
    (rightMarked port inside).erase = port.fill inside.erase := by
  cases shape : port.middle <;> simp only [rightMarked,RightPort.fill,shape,MarkedTree.erase]

@[simp] theorem leftMarked_erase (port : LeftPort α) (inside : MarkedTree α) :
    (leftMarked port inside).erase = port.fill inside.erase := by
  cases shape : port.middle <;> simp only [leftMarked,LeftPort.fill,shape,MarkedTree.erase]

theorem rightMarked_size (port : RightPort α) (inside : MarkedTree α) :
    (rightMarked port inside).skeleton.size ≤ inside.skeleton.size+2 := by
  cases shape : port.middle <;>
    simp only [rightMarked,shape,MarkedTree.skeleton,Tree.size] <;> omega

theorem leftMarked_size (port : LeftPort α) (inside : MarkedTree α) :
    (leftMarked port inside).skeleton.size ≤ inside.skeleton.size+2 := by
  cases shape : port.middle <;>
    simp only [leftMarked,shape,MarkedTree.skeleton,Tree.size] <;> omega

def lowMarked (queue : Option (OpenDeque.Right α)) (inside : MarkedTree α) : MarkedTree α :=
  match queue with
  | none => inside
  | some layout => rightMarked layout.port inside

def highMarked (queue : Option (OpenDeque.Left α)) (inside : MarkedTree α) : MarkedTree α :=
  match queue with
  | none => inside
  | some layout => leftMarked layout.port inside

def TendonContents.Tendon.marked (tendon : Tendon α) (inside : MarkedTree α) : MarkedTree α :=
  lowMarked tendon.lowQueue (highMarked tendon.highQueue inside)

@[simp] theorem lowMarked_erase (queue : Option (OpenDeque.Right α)) (inside : MarkedTree α) :
    (lowMarked queue inside).erase = lowFill queue inside.erase := by
  cases queue with
  | none => rfl
  | some layout => simpa only [lowMarked,lowFill,OpenDeque.Right.fill_tree] using rightMarked_erase layout.port inside

@[simp] theorem highMarked_erase (queue : Option (OpenDeque.Left α)) (inside : MarkedTree α) :
    (highMarked queue inside).erase = highFill queue inside.erase := by
  cases queue with
  | none => rfl
  | some layout => simpa only [highMarked,highFill,OpenDeque.Left.fill_tree] using leftMarked_erase layout.port inside

@[simp] theorem TendonContents.Tendon.marked_erase (tendon : Tendon α) (inside : MarkedTree α) :
    (tendon.marked inside).erase = tendon.fill inside.erase := by
  simp only [Tendon.marked,Tendon.fill,lowMarked_erase,highMarked_erase]

theorem lowMarked_size (queue : Option (OpenDeque.Right α)) (inside : MarkedTree α) :
    (lowMarked queue inside).skeleton.size ≤ inside.skeleton.size+2 := by
  cases queue with
  | none => simp only [lowMarked]; omega
  | some layout => exact rightMarked_size layout.port inside

theorem highMarked_size (queue : Option (OpenDeque.Left α)) (inside : MarkedTree α) :
    (highMarked queue inside).skeleton.size ≤ inside.skeleton.size+2 := by
  cases queue with
  | none => simp only [highMarked]; omega
  | some layout => exact leftMarked_size layout.port inside

theorem TendonContents.Tendon.marked_size (tendon : Tendon α) (inside : MarkedTree α) :
    (tendon.marked inside).skeleton.size ≤ inside.skeleton.size+4 := by
  have first := lowMarked_size tendon.lowQueue (highMarked tendon.highQueue inside)
  have second := highMarked_size tendon.highQueue inside
  exact first.trans (by omega)

end DynamicOptimality.MultiFinger
