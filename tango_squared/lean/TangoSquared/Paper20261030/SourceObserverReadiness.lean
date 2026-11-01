import TangoSquared.Paper20261030.ImmutableReadOnlyRun
import TangoSquared.Paper20261030.StructuralReadiness

/-! Read-only observers may inspect the stored structural fields as well
as payloads. Exact initial annotations suffice for every subsequent
read/navigation instruction; no instruction-level readiness assumptions
are required from the caller. No extra source operation is introduced.
-/

namespace TangoSquared.Paper20261030.Structural

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ η C σ : Type*} [DecidableEq η] [LinearOrder C] [Fintype C]

omit [DecidableEq η] [Fintype C] in
theorem annotate_erase (identifier : ρ → η) (color : α → C) (parent : Option η) (source : Source α ρ) :
    (annotate identifier color parent source).mapRecords Prod.fst = source := by
  induction source generalizing parent <;> simp_all only [annotate,Source.mapRecords]

omit [DecidableEq η] [Fintype C] in
theorem frames_erase (identifier : ρ → η) (color : α → C) (focus : Source α ρ) (outside : List (Frame α ρ)) :
    (frames identifier color focus outside).map (Frame.mapRecords Prod.fst) = outside := by
  induction outside generalizing focus with
  | nil => rfl
  | cons frame rest ih =>
    cases frame <;> simp only [frames,List.map_cons,Frame.mapRecords,annotate_erase,ih]

omit [DecidableEq η] [Fintype C] in
theorem cursor_erase (identifier : ρ → η) (color : α → C) (source : Cursor α ρ) :
    (cursor identifier color source).mapRecords Prod.fst = source := by
  cases source
  simp only [cursor,Cursor.mapRecords,annotate_erase,frames_erase]

theorem observer_checked (identifier : ρ → η) (color : α → C)
    (source : Program σ (ρ × Fields η C)) (readonly : ImmutableSource.ReadOnly source)
    {initial last : σ} {before after : Cursor α (ρ × Fields η C)} {reads cost}
    (run : Run source initial before last after reads cost)
    (plain : Cursor α ρ) (annotated : before = cursor identifier color plain) :
    CheckedRun identifier color source initial before last after reads cost := by
  induction run generalizing plain with
  | halt stopped => exact .halt stopped
  | @next state middle last before current after entry reads cost first rest ih =>
    cases first with
    | read instruction =>
      refine .next (.read instruction) ?_ (ih plain annotated)
      rw [instruction,annotated]
      exact cursor_read_ready identifier color plain _
    | nav instruction moved =>
      rename_i action
      have edge : MultiSourceSingleCursor.EdgeMove action := by
        have h := readonly state
        simpa only [instruction] using h
      have notRight : action ≠ .rotateRight := by intro h; subst action; exact edge
      have notLeft : action ≠ .rotateLeft := by intro h; subst action; exact edge
      have movedPlain : navigate action plain = some (current.mapRecords Prod.fst) := by
        have h := congrArg (Option.map (Cursor.mapRecords Prod.fst)) moved
        rw [navigate_mapRecords,annotated,cursor_erase] at h
        exact h
      have currentAnnotated : current = cursor identifier color (current.mapRecords Prod.fst) := by
        have lifted := Compiler.navigate_direct identifier color action notRight notLeft movedPlain
        rw [← annotated,moved] at lifted
        exact Option.some.inj lifted
      refine .next (.nav instruction moved) ?_ (ih _ currentAnnotated)
      rw [instruction,annotated]
      exact cursor_direct_ready identifier color action notRight notLeft movedPlain _
    | write instruction =>
      have impossible := readonly state
      simp only [instruction] at impossible

end TangoSquared.Paper20261030.Structural
