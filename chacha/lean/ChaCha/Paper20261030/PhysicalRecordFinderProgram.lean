import ChaCha.Paper20261030.PhysicalForestCandidates
import ChaCha.Paper20261030.ForestProgramComposition

/-! A local search of current physical fingers and their parents. Each
color is inspected by the checked parent tour, then (if necessary) by a
current-node read. Identifiers are compared only with records actually
read. A scan uses at most five commands per color. The correctness of the
complete scan is proved separately from this program and its local phases.
-/

namespace ChaCha.Paper20261030.PhysicalRecordFinder

open ColoredStorage SourcePointer ForestLocalProgram Structural PhysicalForestMetadata

variable {α ρ ι η C : Type*} [DecidableEq ι] [DecidableEq η] [LinearOrder C]

inductive State (ρ ι C : Type*) where
  | scan (colors : List C)
  | parent (q : C) (rest : List C) (phase : ParentState ρ ι)
  | current (q : C) (rest : List C)
  | found (record : ρ)

def lookup (identifier : ρ → η) (wanted : η) (entries : Option (List ρ)) : Option ρ :=
  entries.bind (decodeRecord identifier wanted)

def parentResult (identifier : ρ → η) (wanted : η) (q : C) (rest : List C)
    (entries : Option (List ρ)) : State ρ ι C :=
  match lookup identifier wanted entries with
  | none => .current q rest
  | some record => .found record

def currentResult (identifier : ρ → η) (wanted : η) (rest : List C)
    (entries : Option (List ρ)) : State ρ ι C :=
  match lookup identifier wanted entries with
  | none => .scan rest
  | some record => .found record

def afterParent (identifier : ρ → η) (wanted : η) (q : C) (rest : List C) : ParentState ρ ι → State ρ ι C
  | .running .start => .scan (q::rest)
  | .running (.done result) => parentResult identifier wanted q rest (result.map Prod.snd)
  | .error | .running .error => parentResult identifier wanted q rest none
  | phase => .parent q rest phase

def readCurrent (identifier : ρ → η) (wanted : η) (rest : List C) : View (Record ρ ι) → State ρ ι C
  | some ([record],_) => currentResult identifier wanted rest (some record.1.2)
  | _ => currentResult identifier wanted rest none

def program (identifier : ρ → η) (wanted : η) : Program (State ρ ι C) C (Record ρ ι)
  | .scan [] => .halt
  | .scan (q::rest) => (parentProgram q (.running .start)).mapState (afterParent identifier wanted q rest)
  | .parent q rest phase => (parentProgram q phase).mapState (afterParent identifier wanted q rest)
  | .current q rest => .read q (readCurrent identifier wanted rest)
  | .found _ => .halt

def currentEntries (current : Option (Cursor α (Payload ρ ι))) : Option (List ρ) :=
  current.map (fun cursor => cursor.focus.rootRecord.2)

def parentEntries (current : Option (Cursor α (Payload ρ ι))) : Option (List ρ) :=
  current.bind (fun cursor => (ParentObservationController.parentPayload cursor.ancestors).map Prod.snd)

omit [LinearOrder C] in
theorem parent_code (identifier : ρ → η) (wanted : η) (q : C) (rest : List C) (phase : ParentState ρ ι)
    (active : parentProgram q phase ≠ .halt) :
    program identifier wanted (afterParent identifier wanted q rest phase) =
      (parentProgram q phase).mapState (afterParent identifier wanted q rest) := by
  cases phase with
  | error => exact False.elim (active rfl)
  | running phase => cases phase with
    | done | error => exact False.elim (active rfl)
    | start | up | readParent | down => rfl

theorem parent_prefix (identifier : ρ → η) (wanted : η) (q : C) (rest : List C)
    (forest : TaggedForest C α ρ ι) (unique : Unique forest) :
    ∃ reads cost, Steps (program identifier wanted) (.scan (q::rest)) (encode forest)
      (parentResult identifier wanted q rest (parentEntries (forest q))) (encode forest) reads cost ∧ cost ≤ 4 := by
  cases present : forest q with
  | none =>
    have front := (parent_absent q forest present).map_prefix (afterParent identifier wanted q rest)
      (parent_code identifier wanted q rest)
    exact ⟨[],1,front,by decide⟩
  | some current =>
    obtain ⟨reads,cost,run,bounded⟩ := parent_present q forest current present (unique q current present)
    have front := run.map_prefix (afterParent identifier wanted q rest) (parent_code identifier wanted q rest)
    exact ⟨reads,cost,front,bounded⟩

theorem current_prefix (identifier : ρ → η) (wanted : η) (q : C) (rest : List C)
    (forest : TaggedForest C α ρ ι) :
    ∃ reads, Steps (program identifier wanted) (.current q rest) (encode forest)
      (currentResult identifier wanted rest (currentEntries (forest q))) (encode forest) reads 1 := by
  cases present : forest q with
  | none =>
    have first : Step (program identifier wanted) (.current q rest) (encode forest)
        (currentResult identifier wanted rest none) (encode forest) none :=
      .readNone (next := readCurrent identifier wanted rest) rfl (by simp only [encode,present,Option.map_none])
    exact ⟨[],first.prefix⟩
  | some current =>
    have atCursor : encode forest q = some (encodeCursor current) := by simp only [encode,present,Option.map_some]
    have actual := Step.readSome (program := program (ι := ι) identifier wanted) (state := .current q rest)
      (next := readCurrent identifier wanted rest) rfl atCursor
    have first : Step (program identifier wanted) (.current q rest) (encode forest)
        (currentResult identifier wanted rest (some current.focus.rootRecord.2)) (encode forest)
        (some (q,(encodeCursor current).focus.rootRecord)) := by
      simpa only [readCurrent,encodeCursor,SourceForestLift.packet,Cursor.mapRecords,cursor,Source.mapRecords_root,
        annotate_root] using actual
    exact ⟨[(q,(encodeCursor current).focus.rootRecord)],first.prefix⟩

end ChaCha.Paper20261030.PhysicalRecordFinder
