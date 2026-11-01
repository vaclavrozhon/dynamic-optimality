import TangoSquared.Paper20261030.ForestProgramComposition
import TangoSquared.Paper20261030.SourceProgramRecordMap
import TangoSquared.Paper20261030.VirtualCursorSize

/-! Replacing one virtual-color tree by a stored cursor in one physical
header leaf. Each virtual operation first reads that header; a navigation
or update writes the new cursor back. Real-color instructions retain their
actual pointer operations. The fixed-size obligation for the stored
cursor is separate from this operational translation.
-/

namespace TangoSquared.Paper20261030.VirtualHeaderController

open ColoredStorage SourcePointer ForestLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α ρ C σ : Type*} [DecidableEq C]

abbrev Virtual (α ρ : Type*) := Option (Cursor α (List ρ))

inductive Datum (α ρ : Type*) where
  | real (record : ρ)
  | header (current : Virtual α ρ)

def Datum.payload : Datum α ρ → Option ρ
  | .real record => some record
  | .header _ => none

def view (current : Virtual α ρ) : View ρ :=
  current.map (fun c => (c.focus.rootRecord,SourceLocalProgram.isLeaf c.focus))

def encode (virtualColor : C) (key : α) (forest : ProjectionForest.State C α ρ) :
    ProjectionForest.State C α (Datum α ρ) := fun q =>
  if q = virtualColor then some ⟨.leaf key [.header (forest virtualColor)],[]⟩
  else (forest q).map (Cursor.mapRecords (List.map Datum.real))

inductive Operation (ρ : Type*) where
  | nav (action : Move)
  | write (records : List ρ)

def effect (operation : Operation ρ) (current : Virtual α ρ) : Virtual α ρ :=
  current.bind fun c => match operation with
    | .nav action => SourceLocalProgram.navigate action c
    | .write records => some ⟨c.focus.setRoot records,c.ancestors⟩

inductive State (σ α ρ : Type*) where
  | ready (state : σ)
  | commit (next : σ) (current : Virtual α ρ)
  | error

def realRead (next : View ρ → σ) (observed : View (Datum α ρ)) : State σ α ρ :=
  .ready (next (observed.map fun (records,leaf) => (records.filterMap Datum.payload,leaf)))

def virtualRead (next : View ρ → σ) : View (Datum α ρ) → State σ α ρ
  | some ([.header current],_) => .ready (next (view current))
  | _ => .error

def virtualAction (operation : Operation ρ) (next : σ) : View (Datum α ρ) → State σ α ρ
  | some ([.header current],_) => match effect operation current with
    | none => .error
    | some target => .commit next (some target)
  | _ => .error

def program (virtualColor : C) (source : Program σ C ρ) : Program (State σ α ρ) C (Datum α ρ)
  | .ready state => match source state with
    | .halt => .halt
    | .read q next => .read q (if q = virtualColor then virtualRead next else realRead next)
    | .nav q action next => if q = virtualColor then .read q (virtualAction (.nav action) next)
        else .nav q action (.ready next)
    | .write q records next => if q = virtualColor then .read q (virtualAction (.write records) next)
        else .write q (records.map Datum.real) (.ready next)
  | .commit next current => .write virtualColor [.header current] (.ready next)
  | .error => .halt

theorem payload_map (records : List ρ) :
    (records.map (Datum.real (α := α))).filterMap Datum.payload = records := by
  induction records <;> simp_all [Datum.payload]

theorem encode_update_real (virtualColor q : C) (different : q ≠ virtualColor) (key : α)
    (forest : ProjectionForest.State C α ρ) (current : Cursor α (List ρ)) :
    encode virtualColor key (Function.update forest q (some current)) =
      Function.update (encode virtualColor key forest) q (some (current.mapRecords (List.map Datum.real))) := by
  funext other
  by_cases same : other = q
  · subst other; simp [encode,different]
  · by_cases virtual : other = virtualColor
    · subst other; simp [encode,Ne.symm different]
    · simp [encode,virtual,same]

theorem encode_update_virtual (virtualColor : C) (key : α) (forest : ProjectionForest.State C α ρ)
    (current : Virtual α ρ) :
    encode virtualColor key (Function.update forest virtualColor current) =
      Function.update (encode virtualColor key forest) virtualColor (some ⟨.leaf key [.header current],[]⟩) := by
  funext other
  by_cases same : other = virtualColor
  · subst other; simp [encode]
  · simp [encode,same]

theorem commit_run (virtualColor : C) (source : Program σ C ρ) (key : α) (forest : ProjectionForest.State C α ρ)
    (next : σ) (current : Virtual α ρ) :
    Steps (program virtualColor source) (.commit next current) (encode virtualColor key forest)
      (.ready next) (encode virtualColor key (Function.update forest virtualColor current)) [] 1 := by
  rw [encode_update_virtual]
  have present : encode virtualColor key forest virtualColor =
      some ⟨.leaf key [.header (forest virtualColor)],[]⟩ := by simp [encode]
  exact (Step.write (program := program virtualColor source) (fresh := [.header current]) rfl present).prefix

end TangoSquared.Paper20261030.VirtualHeaderController
