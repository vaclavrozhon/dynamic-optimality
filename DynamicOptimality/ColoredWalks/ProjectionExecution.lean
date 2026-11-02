import DynamicOptimality.ColoredWalks.ProjectionGeometry

/-!
# Coalescing finite geometric executions without increasing cost

Every monotone map of finite key universes projects an actual geometric
execution. The map need not be injective or surjective, and unused keys
need not occur in any positive row. The shared complete row zero remains
free through `execution_iff_points`.
-/

namespace DynamicOptimality.Geometry

/-- Extend the finite key map constantly beyond its last key. The empty
source universe has the harmless constant-zero extension. -/
def extendKey {n N : Nat} (f : Fin n → Fin N) (key : Nat) : Nat :=
  if positive : 0 < n then
    (f ⟨min key (n-1),by have := min_le_right key (n-1); omega⟩).val
  else 0

@[simp] theorem extendKey_apply {n N : Nat} (f : Fin n → Fin N) (key : Fin n) :
    extendKey f key.val = (f key).val := by
  have positive : 0 < n := Nat.zero_lt_of_lt key.isLt
  simp only [extendKey,dif_pos positive]
  apply congrArg (fun index : Fin n => (f index).val)
  apply Fin.ext
  change min key.val (n-1) = key.val
  exact min_eq_left (by omega)

theorem extendKey_monotone {n N : Nat} (f : Fin n → Fin N) (mono : Monotone f) :
    Monotone (extendKey f) := by
  intro first second order
  by_cases positive : 0 < n
  · simp only [extendKey,dif_pos positive]
    exact mono (show (⟨min first (n-1),by have := min_le_right first (n-1); omega⟩ : Fin n) ≤
      ⟨min second (n-1),by have := min_le_right second (n-1); omega⟩ from
      min_le_min_right (n-1) order)
  · simp only [extendKey,dif_neg positive,le_refl]

theorem points_mapColumns (f : Nat → Nat) (rows : List (Finset Nat)) (time : Int) :
    points time (rows.map (Finset.image f)) = mapColumns f (points time rows) := by
  induction rows generalizing time with
  | nil => simp [points,mapColumns]
  | cons row rows ih =>
    simp only [List.map_cons,points,ih,mapColumns,Finset.image_union,Finset.image_image,Function.comp_def]

theorem RowsServe.mapColumns {n N : Nat} {requests : List Nat} {rows : List (Finset Nat)}
    (serve : RowsServe n requests rows) (f : Nat → Nat)
    (bounded : ∀ key, key < n → f key < N) :
    RowsServe N (requests.map f) (rows.map (Finset.image f)) := by
  induction serve with
  | nil => exact .nil
  | @cons request row requests rows head tail ih =>
    refine .cons ⟨Finset.mem_image.mpr ⟨request,head.1,rfl⟩,?_⟩ ih
    intro key member
    obtain ⟨original,present,rfl⟩ := Finset.mem_image.mp member
    exact bounded original (head.2 original present)

/-- Actual geometric quotient, preserving request times and decreasing the
number of charged positive-time points. -/
theorem execution_mapColumns {n N cost : Nat} {requests : List Nat}
    (execution : Execution n requests cost) (f : Nat → Nat) (mono : Monotone f)
    (bounded : ∀ key, key < n → f key < N) :
    ∃ projectedCost, projectedCost ≤ cost ∧ Execution N (requests.map f) projectedCost := by
  obtain ⟨rows,serve,charge,satisfied⟩ := execution_iff_points.mp execution
  let mapped := rows.map (Finset.image f)
  have geometry : points 1 mapped = mapColumns f (points 1 rows) := points_mapColumns f rows 1
  refine ⟨(points 1 mapped).card,?_,?_⟩
  · rw [geometry,← charge]
    exact Finset.card_image_le
  · apply execution_iff_points.mpr
    refine ⟨mapped,serve.mapColumns f bounded,rfl,?_⟩
    rw [geometry]
    exact satisfied.mapColumns f mono

/-- Monotone maps between finite key universes may merge keys and omit
unused target keys. No surjectivity or all-keys-visited hypothesis occurs. -/
theorem execution_map_monotone {n N cost : Nat} (f : Fin n → Fin N) (mono : Monotone f)
    (requests : List (Fin n)) (execution : Execution n (requests.map Fin.val) cost) :
    ∃ projectedCost, projectedCost ≤ cost ∧
      Execution N ((requests.map f).map Fin.val) projectedCost := by
  have bounded : ∀ key, key < n → extendKey f key < N := by
    intro key bound
    have value := extendKey_apply f ⟨key,bound⟩
    rw [value]
    exact (f ⟨key,bound⟩).isLt
  obtain ⟨projectedCost,charge,result⟩ := execution_mapColumns execution (extendKey f)
    (extendKey_monotone f mono) bounded
  refine ⟨projectedCost,charge,?_⟩
  simpa only [List.map_map,Function.comp_def,extendKey_apply] using result

end DynamicOptimality.Geometry
