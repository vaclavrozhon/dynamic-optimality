import RectangleSurface

/-!
# The geometric BST model

A point `(key,time)` records one touched key in one request row. A finite
point set is arborally satisfied when every nondegenerate closed rectangle
with two opposite corners in the set contains a third point of the set.
The horizontal row at time zero is an uncharged initialization convention.
The definitions below contain no tree or BST-execution witness.
-/

namespace DynamicOptimality.Geometry

open GreedyMerge.Geometry

abbrev Point := GreedyMerge.Geometry.Point

/-- The standard closed-rectangle condition, including boundary witnesses. -/
def ArborallySatisfied (points : Finset Point) : Prop :=
  ∀ p ∈ points, ∀ q ∈ points, p.1 ≠ q.1 → p.2 ≠ q.2 →
    ∃ r ∈ points, r ≠ p ∧ r ≠ q ∧ Between p.1 q.1 r.1 ∧
      min p.2 q.2 ≤ r.2 ∧ r.2 ≤ max p.2 q.2

def update (height : Nat → Int) (time : Int) (row : Finset Nat) (key : Nat) : Int :=
  if key ∈ row then time else height key

/-- An equivalent local, last-touch-time presentation of geometric rows. -/
inductive SurfaceExecution (n : Nat) :
    (Nat → Int) → Int → List Nat → List (Finset Nat) → Nat → Prop
  | nil (height time) : SurfaceExecution n height time [] [] 0
  | cons {height time requests rows cost request row}
      (satisfied : RowSatisfies height n row) (requested : request ∈ row)
      (rest : SurfaceExecution n (update height time row) (time + 1) requests rows cost) :
      SurfaceExecution n height time (request :: requests) (row :: rows) (row.card + cost)

/-- A purely geometric execution. The rectangle condition is checked on
all points present after each row; no BST is included in this definition. -/
inductive ArboralExecution (n : Nat) :
    Finset Point → Int → List Nat → List (Finset Nat) → Nat → Prop
  | nil (history time) : ArboralExecution n history time [] [] 0
  | cons {history time requests rows cost request row}
      (bounded : ∀ key ∈ row, key < n) (requested : request ∈ row)
      (satisfied : ArborallySatisfied (Augment history time row))
      (rest : ArboralExecution n (Augment history time row) (time + 1) requests rows cost) :
      ArboralExecution n history time (request :: requests) (row :: rows) (row.card + cost)

def baseline (n : Nat) : Finset Point :=
  (Finset.range n).image (fun key => (key, (0 : Int)))

def Execution (n : Nat) (requests : List Nat) (cost : Nat) : Prop :=
  ∃ rows, ArboralExecution n (baseline n) 1 requests rows cost

theorem baseline_satisfied (n : Nat) : ArborallySatisfied (baseline n) := by
  intro p hp q hq _ different
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
  exact (different rfl).elim

theorem baseline_surface (n : Nat) : HasSurface (baseline n) (fun _ => 0) n := by
  constructor
  · intro point member
    obtain ⟨key, inRange, rfl⟩ := Finset.mem_image.mp member
    exact ⟨Finset.mem_range.mp inRange, le_rfl⟩
  · intro key bound
    exact Finset.mem_image.mpr ⟨key, Finset.mem_range.mpr bound, rfl⟩

theorem augment_surface {history : Finset Point} {height : Nat → Int}
    {n : Nat} {time : Int} {row : Finset Nat}
    (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time)
    (bounded : ∀ key ∈ row, key < n) :
    HasSurface (Augment history time row) (update height time row) n := by
  constructor
  · intro point member
    rcases Finset.mem_union.mp member with old | fresh
    · have oldSpec := surface.1 point old
      refine ⟨oldSpec.1, ?_⟩
      by_cases touched : point.1 ∈ row
      · simpa [update, touched] using oldSpec.2.trans (above point.1 oldSpec.1).le
      · simpa [update, touched] using oldSpec.2
    · obtain ⟨key, inRow, rfl⟩ := Finset.mem_image.mp fresh
      exact ⟨bounded key inRow, by simp [update, inRow]⟩
  · intro key bound
    by_cases touched : key ∈ row
    · simpa [update, touched] using new_mem_augment (history := history) (time := time) touched
    · simpa [update, touched] using old_mem_augment (time := time) (row := row) (surface.2 key bound)

theorem update_below_next {height : Nat → Int} {n : Nat} {time : Int} {row : Finset Nat}
    (above : ∀ key, key < n → height key < time) :
    ∀ key, key < n → update height time row key < time + 1 := by
  intro key bound
  unfold update
  split <;> have := above key bound <;> omega

theorem augment_satisfied {history : Finset Point} {n : Nat}
    {time : Int} {row : Finset Nat}
    (old : ArborallySatisfied history)
    (past : ∀ point ∈ history, point.2 < time)
    (fresh : NewRectanglesSatisfied history n time row) :
    ArborallySatisfied (Augment history time row) := by
  intro p hp q hq columns times
  rcases Finset.mem_union.mp hp with hp | hp <;>
    rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := old p hp q hq columns times
    exact ⟨r, old_mem_augment hr, h1, h2, h3, h4, h5⟩
  · obtain ⟨key, member, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := fresh.2 key member p hp columns
    refine ⟨r, hr, h2, h1, ?_, ?_, ?_⟩
    · simpa only [Between, min_comm, max_comm] using h3
    · simpa only [min_eq_left (past p hp).le] using h4
    · simpa only [max_eq_right (past p hp).le] using h5
  · obtain ⟨key, member, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := fresh.2 key member q hq (Ne.symm columns)
    refine ⟨r, hr, h1, h2, h3, ?_, ?_⟩
    · simpa only [min_eq_right (past q hq).le] using h4
    · simpa only [max_eq_left (past q hq).le] using h5
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
    exact (times rfl).elim

theorem new_rectangles_of_augment {history : Finset Point} {n : Nat}
    {time : Int} {row : Finset Nat}
    (past : ∀ point ∈ history, point.2 < time)
    (bounded : ∀ key ∈ row, key < n)
    (satisfied : ArborallySatisfied (Augment history time row)) :
    NewRectanglesSatisfied history n time row := by
  refine ⟨bounded, ?_⟩
  intro key member old oldMember different
  obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ :=
    satisfied (key,time) (new_mem_augment member) old (old_mem_augment oldMember)
      (Ne.symm different) (ne_of_gt (past old oldMember))
  refine ⟨r, hr, h1, h2, h3, ?_, ?_⟩
  · simpa only [min_eq_right (past old oldMember).le] using h4
  · simpa only [max_eq_left (past old oldMember).le] using h5

theorem SurfaceExecution.toArboral {n : Nat} {height : Nat → Int} {time : Int}
    {requests : List Nat} {rows : List (Finset Nat)} {cost : Nat}
    (execution : SurfaceExecution n height time requests rows cost)
    {history : Finset Point} (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time)
    (satisfied : ArborallySatisfied history) :
    ArboralExecution n history time requests rows cost := by
  induction execution generalizing history with
  | nil => exact .nil _ _
  | @cons height time requests rows cost request row valid requested rest ih =>
    have newValid := rectangle_row_sufficient surface above valid
    have past : ∀ point ∈ history, point.2 < time :=
      fun point member => (surface.1 point member).2.trans_lt
        (above point.1 (surface.1 point member).1)
    have augmented := augment_satisfied satisfied past newValid
    exact .cons valid.1 requested augmented
      (ih (augment_surface surface above valid.1) (update_below_next above) augmented)

theorem ArboralExecution.toSurface {n : Nat} {history : Finset Point} {time : Int}
    {requests : List Nat} {rows : List (Finset Nat)} {cost : Nat}
    (execution : ArboralExecution n history time requests rows cost)
    {height : Nat → Int} (surface : HasSurface history height n)
    (above : ∀ key, key < n → height key < time) :
    SurfaceExecution n height time requests rows cost := by
  induction execution generalizing height with
  | nil => exact .nil _ _
  | @cons history time requests rows cost request row bounded requested satisfied rest ih =>
    have past : ∀ point ∈ history, point.2 < time :=
      fun point member => (surface.1 point member).2.trans_lt
        (above point.1 (surface.1 point member).1)
    have valid := rectangle_row_necessary surface (new_rectangles_of_augment past bounded satisfied)
    exact .cons valid requested
      (ih (augment_surface surface above bounded) (update_below_next above))

theorem execution_iff_surface {n : Nat} {requests : List Nat} {cost : Nat} :
    Execution n requests cost ↔
      ∃ rows, SurfaceExecution n (fun _ => 0) 1 requests rows cost := by
  constructor
  · rintro ⟨rows, execution⟩
    exact ⟨rows, execution.toSurface (baseline_surface n) (by intro key bound; omega)⟩
  · rintro ⟨rows, execution⟩
    exact ⟨rows, execution.toArboral (baseline_surface n) (by intro key bound; omega)
      (baseline_satisfied n)⟩

/-- The ordinary finite point set, with one positive-time row per request. -/
def points (time : Int) : List (Finset Nat) → Finset Point
  | [] => ∅
  | row :: rows => row.image (fun key => (key, time)) ∪ points (time + 1) rows

def rowCost (rows : List (Finset Nat)) : Nat := (rows.map Finset.card).sum

def RowsServe (n : Nat) (requests : List Nat) (rows : List (Finset Nat)) : Prop :=
  List.Forall₂ (fun request row => request ∈ row ∧ ∀ key ∈ row, key < n) requests rows

theorem points_lower {rows : List (Finset Nat)} {time : Int} {point : Point}
    (member : point ∈ points time rows) : time ≤ point.2 := by
  induction rows generalizing time with
  | nil => simp [points] at member
  | cons row rows ih =>
    rcases Finset.mem_union.mp member with fresh | later
    · obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp fresh
      exact le_rfl
    · have := ih later
      omega

theorem points_card (time : Int) (rows : List (Finset Nat)) :
    (points time rows).card = rowCost rows := by
  induction rows generalizing time with
  | nil => simp [points, rowCost]
  | cons row rows ih =>
    have disjoint : Disjoint (row.image (fun key => (key,time))) (points (time+1) rows) := by
      apply Finset.disjoint_left.mpr
      intro point first second
      obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp first
      have := points_lower second
      omega
    rw [points, Finset.card_union_of_disjoint disjoint, ih]
    have imageCard : (row.image (fun key => (key,time))).card = row.card :=
      Finset.card_image_of_injective _ (fun _ _ equal => congrArg Prod.fst equal)
    simp only [imageCard, rowCost, List.map_cons, List.sum_cons]

theorem RowsServe.points_bounded {n : Nat} {requests : List Nat} {rows : List (Finset Nat)}
    (serve : RowsServe n requests rows) (time : Int) :
    ∀ point ∈ points time rows, point.1 < n := by
  induction serve generalizing time with
  | nil => simp [points]
  | @cons request row requests rows head tail ih =>
    intro point member
    rcases Finset.mem_union.mp member with fresh | later
    · obtain ⟨key, inRow, rfl⟩ := Finset.mem_image.mp fresh
      exact head.2 key inRow
    · exact ih _ point later

theorem ArborallySatisfied.initialPart {large small : Finset Point} {cut : Int}
    (satisfied : ArborallySatisfied large)
    (included : small ⊆ large)
    (bounded : ∀ point ∈ small, point.2 ≤ cut)
    (closed : ∀ point ∈ large, point.2 ≤ cut → point ∈ small) :
    ArborallySatisfied small := by
  intro p hp q hq columns times
  obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := satisfied p (included hp) q (included hq) columns times
  have below : r.2 ≤ cut := h5.trans (max_le (bounded p hp) (bounded q hq))
  exact ⟨r, closed r hr below, h1, h2, h3, h4, h5⟩

theorem ArboralExecution.spec {n : Nat} {history : Finset Point} {time : Int}
    {requests : List Nat} {rows : List (Finset Nat)} {cost : Nat}
    (execution : ArboralExecution n history time requests rows cost)
    (initial : ArborallySatisfied history) :
    RowsServe n requests rows ∧ rowCost rows = cost ∧
      ArborallySatisfied (history ∪ points time rows) := by
  induction execution with
  | nil => exact ⟨.nil, rfl, by simpa [points] using initial⟩
  | @cons history time requests rows cost request row bounded requested satisfied rest ih =>
    obtain ⟨serve, charge, final⟩ := ih satisfied
    refine ⟨.cons ⟨requested,bounded⟩ serve, ?_, ?_⟩
    · simpa only [rowCost, List.map_cons, List.sum_cons] using congrArg (row.card + ·) charge
    · simpa only [points, Augment, Finset.union_assoc] using final

theorem arboralExecution_of_final {n : Nat} {requests : List Nat} {rows : List (Finset Nat)}
    (serve : RowsServe n requests rows) {history : Finset Point} {time : Int}
    (past : ∀ point ∈ history, point.2 < time)
    (satisfied : ArborallySatisfied (history ∪ points time rows)) :
    ArboralExecution n history time requests rows (rowCost rows) := by
  induction serve generalizing history time with
  | nil => exact .nil _ _
  | @cons request row requests rows head tail ih =>
    have headSatisfied : ArborallySatisfied (Augment history time row) := by
      apply satisfied.initialPart (cut := time)
      · intro point member
        rcases Finset.mem_union.mp member with old | fresh
        · exact Finset.mem_union_left _ old
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ fresh)
      · intro point member
        rcases Finset.mem_union.mp member with old | fresh
        · exact (past point old).le
        · obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp fresh
          exact le_rfl
      · intro point member below
        rcases Finset.mem_union.mp member with old | fresh
        · exact old_mem_augment old
        · rcases Finset.mem_union.mp fresh with now | later
          · exact Finset.mem_union_right _ now
          · have := points_lower later
            omega
    have nextPast : ∀ point ∈ Augment history time row, point.2 < time+1 := by
      intro point member
      rcases Finset.mem_union.mp member with old | fresh
      · have := past point old
        omega
      · obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp fresh
        omega
    have nextSatisfied : ArborallySatisfied (Augment history time row ∪ points (time+1) rows) := by
      simpa only [Augment, points, Finset.union_assoc] using satisfied
    exact .cons head.2 head.1 headSatisfied (ih nextPast nextSatisfied)

theorem execution_iff_final_points {n : Nat} {requests : List Nat} {cost : Nat} :
    Execution n requests cost ↔ ∃ rows,
      RowsServe n requests rows ∧ rowCost rows = cost ∧
      ArborallySatisfied (baseline n ∪ points 1 rows) := by
  constructor
  · rintro ⟨rows, execution⟩
    exact ⟨rows, execution.spec (baseline_satisfied n)⟩
  · rintro ⟨rows, serve, charge, satisfied⟩
    subst cost
    refine ⟨rows, arboralExecution_of_final serve ?_ satisfied⟩
    intro point member
    obtain ⟨key, _, rfl⟩ := Finset.mem_image.mp member
    omega

/-- Adding the complete horizontal initialization row does not change
arboral satisfaction of points at strictly positive times. -/
theorem baseline_union_iff {n : Nat} {set : Finset Point}
    (bounded : ∀ point ∈ set, point.1 < n)
    (positive : ∀ point ∈ set, 0 < point.2) :
    ArborallySatisfied (baseline n ∪ set) ↔ ArborallySatisfied set := by
  constructor
  · intro satisfied p hp q hq columns times
    obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ :=
      satisfied p (Finset.mem_union_right _ hp) q (Finset.mem_union_right _ hq) columns times
    have member : r ∈ set := by
      rcases Finset.mem_union.mp hr with initial | member
      · obtain ⟨key, _, equal⟩ := Finset.mem_image.mp initial
        have atZero : r.2 = 0 := by rw [← equal]
        have pPos := positive p hp
        have qPos := positive q hq
        omega
      · exact member
    exact ⟨r, member, h1, h2, h3, h4, h5⟩
  · intro satisfied p hp q hq columns times
    rcases Finset.mem_union.mp hp with hp | hp <;>
      rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
      exact (times rfl).elim
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
      have qPos := positive q hq
      refine ⟨(q.1,0), Finset.mem_union_left _ ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨q.1, Finset.mem_range.mpr (bounded q hq), rfl⟩
      · intro equal
        exact columns (congrArg Prod.fst equal).symm
      · intro equal
        have := congrArg Prod.snd equal
        omega
      · exact ⟨min_le_right _ _, le_max_right _ _⟩
      · simp only [min_eq_left qPos.le, le_refl]
      · exact le_max_of_le_left le_rfl
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hq
      have pPos := positive p hp
      refine ⟨(p.1,0), Finset.mem_union_left _ ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_range.mpr (bounded p hp), rfl⟩
      · intro equal
        have := congrArg Prod.snd equal
        omega
      · intro equal
        have keyEq : p.1 = b := congrArg Prod.fst equal
        exact columns keyEq
      · exact ⟨min_le_left _ _, le_max_left _ _⟩
      · simp only [min_eq_right pPos.le, le_refl]
      · exact le_max_of_le_right le_rfl
    · obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := satisfied p hp q hq columns times
      exact ⟨r, Finset.mem_union_right _ hr, h1, h2, h3, h4, h5⟩

/-- Standard finite-point-set presentation: positive request rows, required
request points, the usual rectangle condition, and exactly point cardinality
as cost. In particular, the uncharged baseline adds no extra constraint. -/
theorem execution_iff_points {n : Nat} {requests : List Nat} {cost : Nat} :
    Execution n requests cost ↔ ∃ rows,
      RowsServe n requests rows ∧ (points 1 rows).card = cost ∧
      ArborallySatisfied (points 1 rows) := by
  rw [execution_iff_final_points]
  constructor
  · rintro ⟨rows, serve, charge, satisfied⟩
    have positive : ∀ point ∈ points 1 rows, 0 < point.2 := by
      intro point member
      have := points_lower member
      omega
    exact ⟨rows, serve, (points_card 1 rows).trans charge,
      (baseline_union_iff (serve.points_bounded 1) positive).mp satisfied⟩
  · rintro ⟨rows, serve, charge, satisfied⟩
    have positive : ∀ point ∈ points 1 rows, 0 < point.2 := by
      intro point member
      have := points_lower member
      omega
    exact ⟨rows, serve, (points_card 1 rows).symm.trans charge,
      (baseline_union_iff (serve.points_bounded 1) positive).mpr satisfied⟩

end DynamicOptimality.Geometry
