import DynamicOptimality.GeometricOnlineSimulation.OpenDeque
import DynamicOptimality.MultiFinger.TendonDeque

/-!
# Absorbing a newly exposed block frontier

Repeated end insertion consumes a spine in linear amortized rotations.
The original deque may be arbitrarily larger; its untouched cells and its
persistent imbalance potential are retained.
-/

namespace DynamicOptimality.GeometricOnlineSimulation.OpenDeque

open ChaCha.MTR SearchRotation DynamicOptimality.SingleFinger
open DynamicOptimality.MultiFinger.TendonDeque (trailing trailing_append)

variable {α : Type*}

def Right.absorb (outer : Right α) (gap : RawTree α) : List (Spine.Cell α) → Right α
  | [] => outer
  | (key, next) :: rest => (outer.append gap key).absorb next rest

theorem Right.absorb_cells (outer : Right α) (gap : RawTree α) (cells : List (Spine.Cell α)) :
    ((outer.absorb gap cells).fill (trailing gap cells)).cells =
      (outer.fill gap).cells ++ cells := by
  induction cells generalizing outer gap with
  | nil => simp [absorb, trailing]
  | cons cell rest ih =>
      rcases cell with ⟨key, next⟩
      rw [absorb, trailing, ih, append_fill]
      simp only [Deque.pushMaxLayout, Deque.Layout.cells,
        List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

theorem Right.absorb_gap (outer : Right α) (gap : RawTree α) (cells : List (Spine.Cell α)) :
    (outer.absorb gap cells).gap = outer.gap := by
  induction cells generalizing outer gap with
  | nil => rfl
  | cons cell rest ih => exact ih (outer.append gap cell.1) cell.2

theorem Right.absorb_rotations (outer : Right α) (gap : RawTree α) (cells : List (Spine.Cell α)) :
    ∃ count ≤ cells.length,
      Rotations (outer.fill (Spine.rightSpine gap cells)).tree
        ((outer.absorb gap cells).fill (trailing gap cells)).tree count ∧
      count + (outer.absorb gap cells).potential ≤ outer.potential + 5 * cells.length := by
  induction cells generalizing outer gap with
  | nil => exact ⟨0, le_rfl, .refl _, by simp [absorb]⟩
  | cons cell rest ih =>
      rcases cell with ⟨key, next⟩
      obtain ⟨first, firstCount, firstRun, firstBound⟩ :=
        outer.append_rotations gap (Spine.rightSpine next rest) key
      obtain ⟨last, lastCount, lastRun, lastBound⟩ := ih (outer.append gap key) next
      refine ⟨first + last, by simp only [List.length_cons]; omega, firstRun.append lastRun, ?_⟩
      simp only [absorb, List.length_cons]
      omega

def Left.absorb (outer : Left α) (cells : List (Spine.Cell α)) : Left α :=
  { outer with front := cells ++ outer.front }

theorem Left.absorb_append (outer : Left α) (cells : List (Spine.Cell α))
    (key : α) (gap : RawTree α) :
    outer.absorb (cells ++ [(key, gap)]) = (outer.prepend gap key).absorb cells := by
  simp only [absorb, prepend, List.append_assoc, List.singleton_append]

theorem Left.absorb_cells (outer : Left α) (gap : RawTree α) (cells : List (Spine.Cell α)) :
    ((outer.absorb cells).fill gap).cells = cells ++ (outer.fill gap).cells := by
  simp only [absorb, fill, Deque.Layout.cells, List.append_assoc]

theorem Left.absorb_rotations (outer : Left α) (gap : RawTree α) (cells : List (Spine.Cell α)) :
    ∃ count ≤ cells.length,
      Rotations (outer.fill (Spine.leftSpine gap cells)).tree
        ((outer.absorb cells).fill gap).tree count ∧
      count + (outer.absorb cells).potential ≤ outer.potential + 5 * cells.length := by
  induction cells using List.reverseRecOn generalizing outer with
  | nil => exact ⟨0, le_rfl, .refl _, by simp [absorb]⟩
  | append_singleton cells cell ih =>
      rcases cell with ⟨key, next⟩
      obtain ⟨first, firstCount, firstRun, firstBound⟩ :=
        outer.prepend_rotations (Spine.leftSpine gap cells) next key
      obtain ⟨last, lastCount, lastRun, lastBound⟩ := ih (outer.prepend next key)
      refine ⟨first + last, by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
      · simpa only [Spine.leftSpine_append, Spine.leftSpine, absorb_append] using firstRun.append lastRun
      · rw [absorb_append]
        simp only [List.length_append, List.length_singleton]
        omega

end DynamicOptimality.GeometricOnlineSimulation.OpenDeque
