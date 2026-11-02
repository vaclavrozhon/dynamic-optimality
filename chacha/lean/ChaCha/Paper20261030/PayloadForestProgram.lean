import ChaCha.Paper20261030.ForestProgramComposition
import ChaCha.Paper20261030.SourcePayloads

/-! Executable local programs on routing skeletons with attached
unchanged payload trees. The first delimiter separates routing records
from the payload root's records and supplies the logical leaf bit.
Writes read the reached root before replacing only the routing prefix.
The payload assignment is used in the representation proof, not by the
running program.
-/

namespace ChaCha.Paper20261030.SourcePayloads

open ColoredStorage SourcePointer SourceLocalProgram
open DynamicOptimality.LocalProgram (Move)

variable {α β ρ : Type*}

def logicalLeaf (records : List (Option ρ)) : Bool := records.any Option.isNone

theorem logicalLeaf_internal (records : List ρ) : logicalLeaf (records.map some) = false := by
  induction records <;> simp_all [logicalLeaf]

theorem logicalLeaf_attachment (records : List ρ) (payload : List (Option ρ)) :
    logicalLeaf (records.map some ++ none::payload) = true := by
  induction records <;> simp_all [logicalLeaf]

theorem graft_leaf (payload : α → Source β (List (Option ρ))) (source : Source α (List ρ)) :
    logicalLeaf (graft payload source).rootRecord = isLeaf source := by
  cases source with
  | leaf key records =>
    unfold graft
    cases h : payload key <;> exact logicalLeaf_attachment records _
  | fork records l r => exact logicalLeaf_internal records

theorem navigate_graft (payload : α → Source β (List (Option ρ))) (action : Move)
    {before after : Cursor α (List ρ)} (moved : navigate action before = some after) :
    navigate action (cursor payload before) = some (cursor payload after) := by
  rcases before with ⟨focus,outside⟩
  cases action with
  | left => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons first rest => cases first <;> cases Option.some.inj moved <;> rfl
  | rotateRight => cases focus with
    | leaf => simp [navigate] at moved
    | fork q l w => cases l with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl
  | rotateLeft => cases focus with
    | leaf => simp [navigate] at moved
    | fork p u r => cases r with
      | leaf => simp [navigate] at moved
      | fork => cases Option.some.inj moved; rfl

end ChaCha.Paper20261030.SourcePayloads

namespace ChaCha.Paper20261030.PayloadForestController

open ColoredStorage SourcePointer ForestLocalProgram

variable {α β ρ C σ : Type*} [DecidableEq C]

def transform (payload : C → α → Source β (List (Option ρ))) (forest : ProjectionForest.State C α ρ) :
    ProjectionForest.State C β (Option ρ) := fun q => (forest q).map (SourcePayloads.cursor (payload q))

inductive State (σ C ρ : Type*) where
  | ready (state : σ)
  | writing (q : C) (records : List (Option ρ)) (next : σ)
  | error

def readNext (next : View ρ → σ) (observed : View (Option ρ)) : State σ C ρ :=
  .ready (next (observed.map fun (records,_) => (SourcePayloads.decode records,SourcePayloads.logicalLeaf records)))

def writeNext (q : C) (fresh : List ρ) (next : σ) : View (Option ρ) → State σ C ρ
  | none => .error
  | some (records,_) => .writing q (SourcePayloads.replace fresh records) next

def program (source : Program σ C ρ) : Program (State σ C ρ) C (Option ρ)
  | .ready state => match source state with
    | .halt => .halt
    | .read q next => .read q (readNext next)
    | .nav q action next => .nav q action (.ready next)
    | .write q fresh next => .read q (writeNext q fresh next)
  | .writing q records next => .write q records (.ready next)
  | .error => .halt

theorem transform_update (payload : C → α → Source β (List (Option ρ))) (forest : ProjectionForest.State C α ρ)
    (q : C) (current : Cursor α (List ρ)) :
    transform payload (Function.update forest q (some current)) =
      Function.update (transform payload forest) q (some (SourcePayloads.cursor (payload q) current)) := by
  funext other
  by_cases same : other = q
  · subst other; simp [transform]
  · simp only [transform,Function.update_of_ne same]

end ChaCha.Paper20261030.PayloadForestController
