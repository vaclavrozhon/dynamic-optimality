import ChaCha.Paper20261030.LocalPackedRead

/-! The exact physical child move is decided by the two stored child
color masks. It is a move in the requested direction precisely when the
color occurs in both children; otherwise the active or parked finger
stays in place. This refines the earlier existential one-move bound.
-/

namespace ChaCha.Paper20261030.LeafPointer

open RouterProjection
variable {α : Type*} [DecidableEq α]

theorem project_left_idle (keep : α → Bool) (l r : Router α) (rest : List (Frame α))
    (empty : l.prune keep = .empty ∨ r.prune keep = .empty) :
    project keep ⟨l,.left r::rest⟩ = project keep ⟨.fork l r,rest⟩ := by
  rcases empty with hl | hr
  · by_cases hr : r.prune keep = .empty
    · simp only [project,Router.prune,hl,hr,Router.join,ite_true,parked]
    · simp only [project,Router.prune,hl,Router.join,hr,if_false,ite_true,parked]
  · by_cases hl : l.prune keep = .empty
    · simp only [project,Router.prune,hl,hr,Router.join,ite_true,parked]
    · simp only [project,Router.prune,hr,Router.join_empty,hl,if_false,projectedFrames,ite_true]

theorem project_right_idle (keep : α → Bool) (l r : Router α) (rest : List (Frame α))
    (empty : l.prune keep = .empty ∨ r.prune keep = .empty) :
    project keep ⟨r,.right l::rest⟩ = project keep ⟨.fork l r,rest⟩ := by
  rcases empty with hl | hr
  · by_cases hr : r.prune keep = .empty
    · simp only [project,Router.prune,hl,hr,Router.join,ite_true,parked]
    · simp only [project,Router.prune,hl,Router.join,hr,if_false,projectedFrames,ite_true]
  · by_cases hl : l.prune keep = .empty
    · simp only [project,Router.prune,hl,hr,Router.join,ite_true,parked]
    · simp only [project,Router.prune,hr,Router.join_empty,hl,if_false,ite_true,parked]

theorem project_fork_active (keep : α → Bool) (l r : Router α) (rest : List (Frame α))
    (left : l.prune keep ≠ .empty) (right : r.prune keep ≠ .empty) :
    project keep ⟨.fork l r,rest⟩ =
      some ⟨.fork (l.prune keep) (r.prune keep),projectedFrames keep rest⟩ := by
  simp only [project,Router.prune,join_eq_fork left right,reduceCtorEq,if_false]

end ChaCha.Paper20261030.LeafPointer

namespace ChaCha.Paper20261030.ColoredStorage

open SourcePointer RouterProjection SourceLocalProgram
variable {α ρ C : Type*} [DecidableEq α] [LinearOrder C]

omit [DecidableEq α] in
theorem prune_nonempty_iff (color : α → C) (q : C) (source : Source α ρ) :
    source.shape.prune (keepColor color q) ≠ .empty ↔ q ∈ source.support color := by
  change source.shape.prune (fun key => decide (color key = q)) ≠ .empty ↔ _
  rw [← pack_shape]
  exact (not_congr (Stored.shape_eq_empty _)).trans (pack_nonempty color q source)

theorem prune_empty_of_absent (color : α → C) (q : C) (source : Source α ρ)
    (absent : q ∉ source.support color) : source.shape.prune (keepColor color q) = .empty := by
  by_contra present
  exact absent ((prune_nonempty_iff color q source).mp present)

theorem left_idle (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (idle : q ∉ l.support color ∨ q ∉ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨.fork record l r,outside⟩ physical) :
    Represents color q ⟨l,.left record r::outside⟩ physical := by
  refine ⟨represented.1,?_⟩
  have empty : l.shape.prune (keepColor color q) = .empty ∨ r.shape.prune (keepColor color q) = .empty :=
    idle.imp (prune_empty_of_absent color q l) (prune_empty_of_absent color q r)
  have unchanged := LeafPointer.project_left_idle (keepColor color q) l.shape r.shape (outside.map frameShape) empty
  exact unchanged.trans represented.2

theorem right_idle (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (idle : q ∉ l.support color ∨ q ∉ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨.fork record l r,outside⟩ physical) :
    Represents color q ⟨r,.right l record::outside⟩ physical := by
  refine ⟨represented.1,?_⟩
  have empty : l.shape.prune (keepColor color q) = .empty ∨ r.shape.prune (keepColor color q) = .empty :=
    idle.imp (prune_empty_of_absent color q l) (prune_empty_of_absent color q r)
  have unchanged := LeafPointer.project_right_idle (keepColor color q) l.shape r.shape (outside.map frameShape) empty
  exact unchanged.trans represented.2

omit [DecidableEq α] in
theorem lift_left_exact (physical : Cursor α ρ) (l r : Router α) (outside : List (LeafPointer.Frame α))
    (shape : cursorShape physical = ⟨.fork l r,outside⟩) :
    ∃ target, navigate .left physical = some target ∧ SourcePointer.Move physical target ∧
      cursorShape target = ⟨l,.left r::outside⟩ := by
  rcases physical with ⟨focus,rest⟩
  cases focus with
  | leaf => simp [cursorShape,Source.shape] at shape
  | fork record left right =>
    simp only [cursorShape,Source.shape,LeafPointer.Cursor.mk.injEq,Router.fork.injEq] at shape
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := shape
    exact ⟨⟨left,.left record right::rest⟩,rfl,.left _ _ _ _,rfl⟩

omit [DecidableEq α] in
theorem lift_right_exact (physical : Cursor α ρ) (l r : Router α) (outside : List (LeafPointer.Frame α))
    (shape : cursorShape physical = ⟨.fork l r,outside⟩) :
    ∃ target, navigate .right physical = some target ∧ SourcePointer.Move physical target ∧
      cursorShape target = ⟨r,.right l::outside⟩ := by
  rcases physical with ⟨focus,rest⟩
  cases focus with
  | leaf => simp [cursorShape,Source.shape] at shape
  | fork record left right =>
    simp only [cursorShape,Source.shape,LeafPointer.Cursor.mk.injEq,Router.fork.injEq] at shape
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := shape
    exact ⟨⟨right,.right left record::rest⟩,rfl,.right _ _ _ _,rfl⟩

theorem left_active (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (active : q ∈ l.support color ∧ q ∈ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨.fork record l r,outside⟩ physical) :
    ∃ target, navigate .left physical = some target ∧
      Represents color q ⟨l,.left record r::outside⟩ target := by
  have left := (prune_nonempty_iff color q l).mpr active.1
  have right := (prune_nonempty_iff color q r).mpr active.2
  have projected := LeafPointer.project_fork_active (keepColor color q) l.shape r.shape (outside.map frameShape) left right
  have shape := (Option.some.inj (projected.symm.trans represented.2)).symm
  obtain ⟨target,moved,navigation,targetShape⟩ := lift_left_exact physical _ _ _ shape
  refine ⟨target,moved,represented.1.trans (congrArg some navigation.tree),?_⟩
  rw [targetShape]
  simp only [cursorShape,List.map_cons,frameShape,LeafPointer.project,left,if_false,LeafPointer.projectedFrames,right]

theorem right_active (color : α → C) (q : C) (l r : Source α ρ) (record : ρ) (outside)
    (active : q ∈ l.support color ∧ q ∈ r.support color) {physical : Cursor α (List ρ)}
    (represented : Represents color q ⟨.fork record l r,outside⟩ physical) :
    ∃ target, navigate .right physical = some target ∧
      Represents color q ⟨r,.right l record::outside⟩ target := by
  have left := (prune_nonempty_iff color q l).mpr active.1
  have right := (prune_nonempty_iff color q r).mpr active.2
  have projected := LeafPointer.project_fork_active (keepColor color q) l.shape r.shape (outside.map frameShape) left right
  have shape := (Option.some.inj (projected.symm.trans represented.2)).symm
  obtain ⟨target,moved,navigation,targetShape⟩ := lift_right_exact physical _ _ _ shape
  refine ⟨target,moved,represented.1.trans (congrArg some navigation.tree),?_⟩
  rw [targetShape]
  simp only [cursorShape,List.map_cons,frameShape,LeafPointer.project,right,if_false,LeafPointer.projectedFrames,left]

end ChaCha.Paper20261030.ColoredStorage
