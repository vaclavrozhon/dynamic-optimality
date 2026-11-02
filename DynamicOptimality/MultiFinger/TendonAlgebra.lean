import DynamicOptimality.MultiFinger.TendonRegion

/-! Exact source concatenation and marker-word identities for tendons. -/

namespace DynamicOptimality.MultiFinger

open ChaCha.MTR
open Pointer (MarkedTree)
open GeometricOnlineSimulation.OpenDeque
open TendonContents TendonSource

variable {α : Type*}

theorem low_append (first last : List (Pointer.Frame α)) :
    low (first++last) = low last++low first := by
  induction first with
  | nil => simp [low]
  | cons frame frames ih => cases frame <;> simp [low,ih,List.append_assoc]

theorem high_append (first last : List (Pointer.Frame α)) :
    high (first++last) = high first++high last := by
  induction first with
  | nil => rfl
  | cons frame frames ih => cases frame <;> simp [high,ih]

theorem DataEquivalent.low {before after : MarkedTree α} (same : DataEquivalent before after)
    (queue : Option (Right α)) : DataEquivalent (lowMarked queue before) (lowMarked queue after) := by
  exact ⟨by simp only [lowMarked_word,same.1],by simp only [lowMarked_holes,same.2]⟩

theorem DataEquivalent.high {before after : MarkedTree α} (same : DataEquivalent before after)
    (queue : Option (Left α)) : DataEquivalent (highMarked queue before) (highMarked queue after) := by
  exact ⟨by simp only [highMarked_word,same.1],by simp only [highMarked_holes,same.2]⟩

theorem low_node (queue : Option (Right α)) (left right : MarkedTree α) (key : α) :
    DataEquivalent (lowMarked queue (.node left key right)) (.node (lowMarked queue left) key right) := by
  constructor <;> simp [lowMarked_word,lowMarked_holes,MarkedTree.skeleton,Tree.inorder,MarkedTree.holes,List.append_assoc]

theorem high_node (queue : Option (Left α)) (left right : MarkedTree α) (key : α) :
    DataEquivalent (highMarked queue (.node left key right)) (.node left key (highMarked queue right)) := by
  constructor <;> simp [highMarked_word,highMarked_holes,MarkedTree.skeleton,Tree.inorder,MarkedTree.holes,List.append_assoc]

theorem low_high (lowQueue : Option (Right α)) (highQueue : Option (Left α)) (inside : MarkedTree α) :
    DataEquivalent (lowMarked lowQueue (highMarked highQueue inside))
      (highMarked highQueue (lowMarked lowQueue inside)) := by
  constructor <;> simp [lowMarked_word,lowMarked_holes,highMarked_word,highMarked_holes,List.append_assoc]

namespace TendonContents

def emptyTendon : Tendon α := ⟨none,none⟩

@[simp] theorem emptyTendon_marked (inside : MarkedTree α) : emptyTendon.marked inside = inside := rfl
@[simp] theorem emptyTendon_potential : (emptyTendon : Tendon α).potential = 0 := rfl

theorem emptyTendon_valid : (emptyTendon : Tendon α).Represents [] := ⟨rfl,rfl⟩

theorem lowValid_nonempty {layout : Right α} {cells : List (LowCell α)}
    (valid : LowValid layout cells) : cells ≠ [] := by
  intro empty
  subst cells
  have sizes := congrArg List.length (valid .empty).2
  simp only [afterCells,SingleFinger.Deque.Layout.cells,List.length_append,List.length_cons,List.length_nil] at sizes
  omega

theorem highValid_nonempty {layout : Left α} {cells : List (HighCell α)}
    (valid : HighValid layout cells) : cells ≠ [] := by
  intro empty
  subst cells
  have sizes := congrArg List.length (valid .empty)
  simp only [SingleFinger.Deque.Layout.cells,List.length_append,List.length_cons,List.length_nil] at sizes
  omega

theorem Tendon.eq_empty {tendon : Tendon α} (valid : tendon.Represents []) : tendon = emptyTendon := by
  have lowEmpty : tendon.lowQueue = none := by
    cases shape : tendon.lowQueue with
    | none => rfl
    | some layout =>
        have impossible : LowValid layout [] := by simpa only [Tendon.Represents,shape,LowRep,low] using valid.1
        exact False.elim (lowValid_nonempty impossible rfl)
  have highEmpty : tendon.highQueue = none := by
    cases shape : tendon.highQueue with
    | none => rfl
    | some layout =>
        have impossible : HighValid layout [] := by simpa only [Tendon.Represents,shape,HighRep,high] using valid.2
        exact False.elim (highValid_nonempty impossible rfl)
  cases tendon
  simp_all [emptyTendon]

end TendonContents
end DynamicOptimality.MultiFinger
