import ChaCha.Paper20261030.MultiSourceRecordMap

/-! A charged visit to a nearby ancestor root, followed by return to the
original vertex. The controller receives a short direction list and a
record-edit function. It reads the root before editing and never observes
a tree or zipper. Component headers use direction lists of length at most
two, so the complete visit costs at most six operations.
-/

namespace ChaCha.Paper20261030.RootRecordTour

open ColoredStorage SourcePointer SourcePositions SourceLocalProgram

variable {α ρ τ : Type*}

inductive State (ρ : Type*) where
  | ascending (remaining : Nat)
  | reading
  | writing (record : ρ)
  | descending (path : List Bool)
  | done

def ascend : Nat → State ρ
  | 0 => .reading
  | n+1 => .ascending n

def descendState : List Bool → State ρ
  | [] => .done
  | path => .descending path

def program (edit : ρ → ρ) (path : List Bool) : Program (State ρ) ρ
  | .ascending remaining => .nav .up (ascend remaining)
  | .reading => .read (fun record _ => .writing (edit record))
  | .writing record => .write record (descendState path)
  | .descending [] => .halt
  | .descending (right::rest) => .nav (if right then .right else .left) (descendState rest)
  | .done => .halt

theorem ascend_steps (edit : ρ → ρ) (path : List Bool) (focus : Source α ρ)
    (inside outside : List (Frame α ρ)) :
    Steps (program edit path) (ascend inside.length) ⟨focus,inside++outside⟩
      .reading ⟨plug focus inside,outside⟩ [] inside.length := by
  induction inside generalizing focus with
  | nil => exact .nil _ _
  | cons frame rest ih => cases frame with
    | left record sibling =>
      exact .next (program := program edit path) (.nav rfl rfl) (ih (.fork record focus sibling))
    | right sibling record =>
      exact .next (program := program edit path) (.nav rfl rfl) (ih (.fork record sibling focus))

theorem descend_run (edit : ρ → ρ) (path rest : List Bool) (before after : Cursor α ρ)
    (reached : SourcePositions.descend before rest = some after) :
    Run (program edit path) (descendState rest) before .done after [] rest.length := by
  induction rest generalizing before with
  | nil => cases Option.some.inj reached; exact .halt rfl
  | cons right rest ih =>
    cases moved : navigate (if right then .right else .left) before with
    | none => simp only [SourcePositions.descend,moved,Option.bind_none,reduceCtorEq] at reached
    | some middle =>
      have tail := ih middle (by simpa only [SourcePositions.descend,moved,Option.bind_some] using reached)
      exact .next (program := program edit path) (.nav rfl moved) tail

theorem run (erase : ρ → τ) (edit : ρ → ρ) (preserved : ∀ record, erase (edit record) = erase record)
    (path : List Bool) (current : Cursor α ρ) (known : path = address current) :
    ∃ target,
      Run (program edit path) (ascend path.length) current .done target [current.tree.rootRecord] (2*path.length+2) ∧
      target.tree = current.tree.setRoot (edit current.tree.rootRecord) ∧ target.mapRecords erase = current.mapRecords erase := by
  let changed := current.tree.setRoot (edit current.tree.rootRecord)
  have same : changed.mapRecords erase = current.tree.mapRecords erase := by
    simp only [changed,Source.mapRecords_setRoot,preserved]
    rw [← Source.mapRecords_root erase current.tree]
    cases current.tree.mapRecords erase <;> rfl
  have located : locate (changed.mapRecords erase) path = some (current.mapRecords erase) := by
    rw [same,known,locate_mapRecords,locate_cursor]
    rfl
  obtain ⟨target,reached,erased⟩ := lift_locate erase changed path (current.mapRecords erase) located
  have first := ascend_steps edit path current.focus current.ancestors []
  have length : path.length = current.ancestors.length := by
    rw [known,address,List.length_map,List.length_reverse]
  have read : Step (program edit path) .reading ⟨current.tree,[]⟩
      (.writing (edit current.tree.rootRecord)) ⟨current.tree,[]⟩ (some current.tree.rootRecord) :=
    .read (next := fun record _ => State.writing (edit record)) rfl
  have write : Step (program edit path) (.writing (edit current.tree.rootRecord)) ⟨current.tree,[]⟩
      (descendState path) ⟨changed,[]⟩ none := .write rfl
  have last := descend_run edit path path ⟨changed,[]⟩ target reached
  have body := read.prefix.append (write.prefix)
  have whole := (first.append body).then_run last
  refine ⟨target,?_,locate_tree reached,erased⟩
  simpa only [List.append_nil,List.nil_append,Cursor.tree,← length,List.singleton_append,
    Option.toList_some,Option.toList_none,Nat.mul_succ,Nat.add_assoc,Nat.two_mul,Nat.add_left_comm,Nat.add_comm] using whole

end ChaCha.Paper20261030.RootRecordTour
