import DynamicOptimality.GeometricOnlineSimulation.Ports
import DynamicOptimality.SingleFinger.DequeEndpoints

/-!
# Deques with a variable end subtree

The original deque algorithms supply the persistent imbalance potential.
An arriving separator at the open end can be absorbed using at most one
rotation. The arbitrary tree following that separator becomes the new port.
-/

namespace DynamicOptimality.GeometricOnlineSimulation.OpenDeque

open ChaCha.MTR SearchRotation
open DynamicOptimality.SingleFinger

variable {α : Type*}

structure Right (α : Type*) where
  gap : RawTree α
  front : List (Spine.Cell α)
  pivot : α
  back : Option (RawTree α × List (Spine.Cell α) × α)

def Right.fill (layout : Right α) (lastGap : RawTree α) : Deque.Layout α :=
  match layout.back with
  | none => ⟨layout.gap, layout.front, layout.pivot, lastGap, []⟩
  | some (afterGap, back, last) =>
      ⟨layout.gap, layout.front, layout.pivot, afterGap, back ++ [(last, lastGap)]⟩

def Right.port (layout : Right α) : RightPort α :=
  ⟨Spine.rightSpine layout.gap layout.front, layout.pivot,
    layout.back.map (fun (afterGap, back, last) => (Spine.leftSpine afterGap back, last))⟩

def Right.potential (layout : Right α) : Nat := (layout.fill .empty).potential

@[simp] theorem Right.fill_tree (layout : Right α) (lastGap : RawTree α) :
    (layout.fill lastGap).tree = layout.port.fill lastGap := by
  cases layout with
  | mk gap front pivot back =>
      cases back with
      | none => rfl
      | some data =>
          rcases data with ⟨afterGap, back, last⟩
          simp [fill, port, RightPort.fill, Deque.Layout.tree,
            Spine.leftSpine_append, Spine.leftSpine]

@[simp] theorem Right.fill_potential (layout : Right α) (lastGap : RawTree α) :
    (layout.fill lastGap).potential = layout.potential := by
  cases layout with
  | mk gap front pivot back =>
      cases back with
      | none => rfl
      | some data =>
          rcases data with ⟨afterGap, back, last⟩
          simp only [fill, potential, Deque.Layout.potential,
            List.length_append, List.length_singleton]

def Right.append (layout : Right α) (beforeGap : RawTree α) (key : α) : Right α :=
  { layout with back := some (match layout.back with
    | none => (beforeGap, [], key)
    | some (afterGap, back, last) => (afterGap, back ++ [(last, beforeGap)], key)) }

theorem Right.append_fill (layout : Right α) (beforeGap afterGap : RawTree α) (key : α) :
    (layout.append beforeGap key).fill afterGap =
      Deque.pushMaxLayout (layout.fill beforeGap) key afterGap := by
  cases layout with
  | mk gap front pivot back =>
      cases back with
      | none => rfl
      | some data =>
          rcases data with ⟨start, back, last⟩
          simp only [append, fill, Deque.pushMaxLayout, List.append_assoc]

theorem Right.append_potential (layout : Right α) (beforeGap : RawTree α) (key : α) :
    (layout.append beforeGap key).potential ≤ layout.potential + 4 := by
  have bound := Deque.push_max_amortized (layout.fill beforeGap) key beforeGap
  rw [← layout.append_fill beforeGap beforeGap key, fill_potential, fill_potential] at bound
  omega

theorem Right.append_rotations (layout : Right α) (beforeGap afterGap : RawTree α) (key : α) :
    ∃ count ≤ 1, Rotations (layout.fill (.node beforeGap key afterGap)).tree
      ((layout.append beforeGap key).fill afterGap).tree count ∧
      count + (layout.append beforeGap key).potential ≤ layout.potential + 5 := by
  have potentialBound := layout.append_potential beforeGap key
  cases layout with
  | mk gap front pivot back =>
      cases back with
      | none => exact ⟨0, by omega, .refl _, by omega⟩
      | some data =>
          rcases data with ⟨start, back, last⟩
          refine ⟨1, le_rfl, ?_, by omega⟩
          simpa only [fill, append, Deque.Layout.tree, Spine.leftSpine_append,
            Spine.leftSpine] using Rotations.singleton
              (Rotation.rightContext (Spine.rightSpine gap front) pivot
                (Rotation.rootLeft (Spine.leftSpine start back) beforeGap afterGap last key))

structure Left (α : Type*) where
  front : List (Spine.Cell α)
  pivot : α
  afterGap : RawTree α
  back : List (Spine.Cell α)

def Left.fill (layout : Left α) (firstGap : RawTree α) : Deque.Layout α :=
  ⟨firstGap, layout.front, layout.pivot, layout.afterGap, layout.back⟩

def Left.port (layout : Left α) : LeftPort α :=
  ⟨layout.pivot, Spine.leftSpine layout.afterGap layout.back,
    match layout.front with
    | [] => none
    | (key, gap) :: rest => some (key, Spine.rightSpine gap rest)⟩

def Left.potential (layout : Left α) : Nat := (layout.fill .empty).potential

@[simp] theorem Left.fill_tree (layout : Left α) (firstGap : RawTree α) :
    (layout.fill firstGap).tree = layout.port.fill firstGap := by
  cases layout with
  | mk front pivot afterGap back => cases front with
    | nil => rfl
    | cons cell rest => cases cell; rfl

@[simp] theorem Left.fill_potential (layout : Left α) (firstGap : RawTree α) :
    (layout.fill firstGap).potential = layout.potential := rfl

def Left.prepend (layout : Left α) (afterGap : RawTree α) (key : α) : Left α :=
  { layout with front := (key, afterGap) :: layout.front }

theorem Left.prepend_fill (layout : Left α) (beforeGap afterGap : RawTree α) (key : α) :
    (layout.prepend afterGap key).fill beforeGap =
      Deque.pushMinLayout (layout.fill afterGap) key beforeGap := rfl

theorem Left.prepend_potential (layout : Left α) (afterGap : RawTree α) (key : α) :
    (layout.prepend afterGap key).potential ≤ layout.potential + 4 := by
  have bound := Deque.push_min_amortized (layout.fill afterGap) key afterGap
  rw [← layout.prepend_fill afterGap afterGap key, fill_potential, fill_potential] at bound
  omega

theorem Left.prepend_rotations (layout : Left α) (beforeGap afterGap : RawTree α) (key : α) :
    ∃ count ≤ 1, Rotations (layout.fill (.node beforeGap key afterGap)).tree
      ((layout.prepend afterGap key).fill beforeGap).tree count ∧
      count + (layout.prepend afterGap key).potential ≤ layout.potential + 5 := by
  have potentialBound := layout.prepend_potential afterGap key
  cases layout with
  | mk front pivot finalGap back =>
      cases front with
      | nil => exact ⟨0, by omega, .refl _, by omega⟩
      | cons cell rest =>
          rcases cell with ⟨first, middle⟩
          exact ⟨1, le_rfl, .singleton (.leftContext
            (.rootRight beforeGap afterGap (Spine.rightSpine middle rest) key first)
            pivot (Spine.leftSpine finalGap back)), by omega⟩

end DynamicOptimality.GeometricOnlineSimulation.OpenDeque
