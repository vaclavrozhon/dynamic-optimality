import ChaCha.Paper20261030.LocalStructuralParent

/-! A charged parent observation on an annotated physical tree. The
controller reads the current parent flag, visits the parent when present,
and returns along the edge selected by comparing child identifiers. It
needs one temporary identifier and one record, with no path stack.
This helper supplies an actual local implementation of a parent tour;
instantiating its physical annotations in the packed forest is separate.
-/

namespace ChaCha.Paper20261030.Structural.ParentObservationController

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι C : Type*} [DecidableEq C] [DecidableEq ι]

inductive State (ρ ι : Type*) where
  | start
  | up (old : ι)
  | readParent (old : ι)
  | down (left : Bool) (record : ρ)
  | done (parent : Option ρ)
  | error

def fromRoot (identifier : ρ → ι) (record : ρ × Fields ι C) : State ρ ι :=
  match record.2.parent with
  | none => .done none
  | some _ => .up (identifier record.1)

def fromParent (old : ι) (record : ρ × Fields ι C) : State ρ ι :=
  match record.2.children with
  | none => .error
  | some (l,_) => .down (decide (l.id = old)) record.1

def program (identifier : ρ → ι) : Program (State ρ ι) (ρ × Fields ι C)
  | .start => .read (fun record _ => fromRoot identifier record)
  | .up old => .nav .up (.readParent old)
  | .readParent old => .read (fun record _ => fromParent old record)
  | .down left record => .nav (if left then .left else .right) (.done (some record))
  | .done _ | .error => .halt

def parentPayload : List (Frame α ρ) → Option ρ
  | [] => none
  | .left record _::_ => some record
  | .right _ record::_ => some record

theorem observe (identifier : ρ → ι) (color : α → C) (focus : Source α ρ) (outside : List (Frame α ρ))
    (unique : ((plug focus outside).inventory identifier).Nodup) :
    ∃ reads cost, Run (program identifier) .start (cursor identifier color ⟨focus,outside⟩)
      (.done (parentPayload outside)) (cursor identifier color ⟨focus,outside⟩) reads cost ∧ cost ≤ 4 := by
  cases outside with
  | nil =>
    have first : SourceLocalProgram.Step (program identifier) .start (cursor identifier color ⟨focus,[]⟩)
        (.done none) (cursor identifier color ⟨focus,[]⟩)
        (some (annotate identifier color none focus).rootRecord) := by
      have actual := SourceLocalProgram.Step.read (program := program (C := C) identifier) (state := .start)
        (cursor := cursor identifier color ⟨focus,[]⟩) (next := fun record _ => fromRoot identifier record) rfl
      simpa only [cursor,parentId,annotate_root,fromRoot,fields] using actual
    exact ⟨[(annotate identifier color none focus).rootRecord],1,.next first (.halt rfl),by decide⟩
  | cons frame rest =>
    cases frame with
    | left record sibling =>
      let A := annotate identifier color (some (identifier record)) focus
      let R := annotate identifier color (some (identifier record)) sibling
      let P := (record,fields identifier color (parentId identifier rest) (.fork record focus sibling))
      let tail := frames identifier color (.fork record focus sibling) rest
      let code := program (C := C) identifier
      have first : SourceLocalProgram.Step code .start ⟨A,.left P R::tail⟩
          (.up (identifier focus.rootRecord)) ⟨A,.left P R::tail⟩ (some A.rootRecord) := by
        have actual := SourceLocalProgram.Step.read (program := code) (state := .start)
          (cursor := (⟨A,.left P R::tail⟩ : Cursor α (ρ × Fields ι C)))
          (next := fun entry _ => fromRoot identifier entry) rfl
        simpa only [A,annotate_root,fromRoot,fields] using actual
      have parentRead : SourceLocalProgram.Step code (.readParent (identifier focus.rootRecord))
          ⟨.fork P A R,tail⟩ (.down true record) ⟨.fork P A R,tail⟩ (some P) := by
        have actual := SourceLocalProgram.Step.read (program := code) (state := .readParent (identifier focus.rootRecord))
          (cursor := (⟨.fork P A R,tail⟩ : Cursor α (ρ × Fields ι C)))
          (next := fun entry _ => fromParent (identifier focus.rootRecord) entry) rfl
        simpa only [Source.rootRecord,P,fromParent,fields,descriptor,decide_true] using actual
      have run : Run code .start ⟨A,.left P R::tail⟩ (.done (some record))
          ⟨A,.left P R::tail⟩ [A.rootRecord,P] 4 :=
        Run.next first (Run.next (program := code) (.nav rfl rfl)
          (Run.next parentRead (Run.next (program := code) (.nav rfl rfl) (.halt rfl))))
      exact ⟨[A.rootRecord,P],4,run,le_rfl⟩
    | right sibling record =>
      have nodeUnique : ((Source.fork record sibling focus).inventory identifier).Nodup :=
        Multiset.nodup_of_le (inventory_le_plug identifier _ rest) unique
      have distinct := child_ids_distinct identifier record sibling focus nodeUnique
      let A := annotate identifier color (some (identifier record)) focus
      let L := annotate identifier color (some (identifier record)) sibling
      let P := (record,fields identifier color (parentId identifier rest) (.fork record sibling focus))
      let tail := frames identifier color (.fork record sibling focus) rest
      let code := program (C := C) identifier
      have first : SourceLocalProgram.Step code .start ⟨A,.right L P::tail⟩
          (.up (identifier focus.rootRecord)) ⟨A,.right L P::tail⟩ (some A.rootRecord) := by
        have actual := SourceLocalProgram.Step.read (program := code) (state := .start)
          (cursor := (⟨A,.right L P::tail⟩ : Cursor α (ρ × Fields ι C)))
          (next := fun entry _ => fromRoot identifier entry) rfl
        simpa only [A,annotate_root,fromRoot,fields] using actual
      have parentRead : SourceLocalProgram.Step code (.readParent (identifier focus.rootRecord))
          ⟨.fork P L A,tail⟩ (.down false record) ⟨.fork P L A,tail⟩ (some P) := by
        have actual := SourceLocalProgram.Step.read (program := code) (state := .readParent (identifier focus.rootRecord))
          (cursor := (⟨.fork P L A,tail⟩ : Cursor α (ρ × Fields ι C)))
          (next := fun entry _ => fromParent (identifier focus.rootRecord) entry) rfl
        have decoded : fromParent (identifier focus.rootRecord) P = .down false record := by
          simp only [P,fromParent,fields,descriptor,distinct,decide_false]
        change SourceLocalProgram.Step code (.readParent (identifier focus.rootRecord))
          ⟨.fork P L A,tail⟩ (fromParent (identifier focus.rootRecord) P) ⟨.fork P L A,tail⟩ (some P) at actual
        rw [decoded] at actual
        exact actual
      have run : Run code .start ⟨A,.right L P::tail⟩ (.done (some record))
          ⟨A,.right L P::tail⟩ [A.rootRecord,P] 4 :=
        Run.next first (Run.next (program := code) (.nav rfl rfl)
          (Run.next parentRead (Run.next (program := code) (.nav rfl rfl) (.halt rfl))))
      exact ⟨[A.rootRecord,P],4,run,le_rfl⟩

end ChaCha.Paper20261030.Structural.ParentObservationController
