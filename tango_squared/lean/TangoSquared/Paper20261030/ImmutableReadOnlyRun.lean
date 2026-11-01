import TangoSquared.Paper20261030.ImmutableSourceProgram
import TangoSquared.Paper20261030.MultiSourceStationaryFingers

/-! A read-only source traversal also preserves the entire tree carrying
immutable identifiers, not just its erased payloads or identifier word.
This is needed when terminal exposure leaves the root but a later primary
header must still name the same logical root vertex.
-/

namespace TangoSquared.Paper20261030.ImmutableSource

open ColoredStorage SourcePointer SourceLocalProgram
open MultiSourceSingleCursor (EdgeMove)

variable {α ρ ι σ : Type*}

def ReadOnly (source : Program σ ρ) : Prop := ∀ state, match source state with
  | .nav move _ => EdgeMove move
  | .write _ _ => False
  | _ => True

theorem edge_tree (move : DynamicOptimality.LocalProgram.Move) {before after : Cursor α ρ}
    (edge : EdgeMove move) (moved : navigate move before = some after) : after.tree = before.tree := by
  rcases before with ⟨focus,outside⟩
  cases move with
  | rotateLeft | rotateRight => exact False.elim edge
  | left | right => cases focus with
    | leaf => simp [navigate] at moved
    | fork => cases Option.some.inj moved; rfl
  | up => cases outside with
    | nil => simp [navigate] at moved
    | cons frame rest => cases frame <;> cases Option.some.inj moved <;> rfl

theorem readonly_step (source : Program σ ρ) (readonly : ReadOnly source)
    {state next : σ} {before after : Cursor α ρ} {entry}
    (step : Step source state before next after entry)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before) :
    ∃ target actualEntry, Step (program source) (.ready state) decorated (.ready next) target actualEntry ∧
      target.mapRecords Prod.snd = after ∧ target.tree = decorated.tree := by
  cases step with
  | read instruction =>
    rename_i nextRead
    have actual : Step (program source) (.ready state) decorated
        (.ready (nextRead decorated.focus.rootRecord.2 (isLeaf decorated.focus))) decorated
        (some decorated.focus.rootRecord) :=
      .read (next := fun (record : ι × ρ) leaf => State.ready (nextRead record.2 leaf))
        (by simp only [program,instruction])
    refine ⟨decorated,some decorated.focus.rootRecord,?_,erases,rfl⟩
    simpa only [← erases,Cursor.mapRecords,Source.mapRecords_root,isLeaf_mapRecords] using actual
  | nav instruction moved =>
    rename_i move
    obtain ⟨target,actualMove,targetErases⟩ := lift_navigation Prod.snd move decorated after (erases ▸ moved)
    have edge : EdgeMove move := by have h := readonly state; simpa only [instruction] using h
    exact ⟨target,none,.nav (by simp only [program,instruction]) actualMove,targetErases,edge_tree move edge actualMove⟩
  | write instruction =>
    have impossible := readonly state
    simp only [instruction] at impossible

theorem readonly_run (source : Program σ ρ) (readonly : ReadOnly source)
    {state last : σ} {before after : Cursor α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (decorated : Cursor α (ι × ρ)) (erases : decorated.mapRecords Prod.snd = before) :
    ∃ target actualReads, Run (program source) (.ready state) decorated (.ready last) target actualReads cost ∧
      target.mapRecords Prod.snd = after ∧ target.tree = decorated.tree := by
  induction run generalizing decorated with
  | halt stopped => exact ⟨decorated,[],.halt (by simp only [program,stopped]),erases,rfl⟩
  | next first rest ih =>
    obtain ⟨middle,entry,firstRun,middleErases,firstTree⟩ := readonly_step source readonly first decorated erases
    obtain ⟨target,entries,lastRun,lastErases,lastTree⟩ := ih middle middleErases
    exact ⟨target,_,.next firstRun lastRun,lastErases,lastTree.trans firstTree⟩

end TangoSquared.Paper20261030.ImmutableSource
