import ChaCha.Paper20261030.MultiSourcePairSteps
import ChaCha.Paper20261030.ForestProgramComposition

/-! A fixed connector layout for the present color components. Layout
leaves name colors; connector records are empty. Evaluation replaces each
layout leaf by the whole tree of that color cursor and retains its finger
position. The layout and whole cursors are ghost representation data, not
arguments to the compiled local program.
-/

namespace ChaCha.Paper20261030.ForestConnector

open ColoredStorage SourcePointer SourcePositions

variable {α ρ C σ : Type*} [DecidableEq C]

def single (q : C) (current : Cursor α (List ρ)) : MultiSourceProgram.Configuration C α (List ρ) :=
  ⟨current.tree,fun other => if other = q then some (address current) else none⟩

def colors (layout : Source C Unit) : List C := layout.shape.leaves

def assemble (forest : ProjectionForest.State C α ρ) : Source C Unit → Option (MultiSourceProgram.Configuration C α (List ρ))
  | .leaf q _ => (forest q).map (single q)
  | .fork _ left right => (assemble forest left).bind fun l =>
      (assemble forest right).map (MultiSourceProgram.join [] l)

def program (source : ForestLocalProgram.Program σ C ρ) : MultiSourceProgram.Program σ C (List ρ) := fun state =>
  match source state with
  | .halt => .halt
  | .read q next => .read q next
  | .nav q action next => .nav q action next
  | .write q fresh next => .write q fresh next

theorem single_wellFormed (q : C) (current : Cursor α (List ρ)) : MultiSourceProgram.WellFormed (single q current) := by
  intro other position present
  by_cases same : other = q
  · subst other
    have equal : address current = position := by simpa only [single,ite_true,Option.some.injEq] using present
    subst position
    exact ⟨current,locate_cursor current⟩
  · simp only [single,same,if_false,reduceCtorEq] at present

theorem assemble_fork {forest : ProjectionForest.State C α ρ} {value : Unit} {left right : Source C Unit}
    {config : MultiSourceProgram.Configuration C α (List ρ)}
    (represented : assemble forest (.fork value left right) = some config) :
    ∃ l r, assemble forest left = some l ∧ assemble forest right = some r ∧ MultiSourceProgram.join [] l r = config := by
  cases leftResult : assemble forest left with
  | none => simp only [assemble,leftResult,Option.bind_none,reduceCtorEq] at represented
  | some l => cases rightResult : assemble forest right with
    | none => simp only [assemble,leftResult,rightResult,Option.bind_some,Option.map_none,reduceCtorEq] at represented
    | some r =>
      exact ⟨l,r,rfl,rfl,by simpa only [assemble,leftResult,rightResult,Option.bind_some,Option.map_some,Option.some.injEq] using represented⟩

theorem assemble_wellFormed (forest : ProjectionForest.State C α ρ) (layout : Source C Unit)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble forest layout = some config) :
    MultiSourceProgram.WellFormed config := by
  induction layout generalizing config with
  | leaf q value =>
    cases location : forest q with
    | none => simp only [assemble,location,Option.map_none,reduceCtorEq] at represented
    | some current =>
      have equal : single q current = config := by simpa only [assemble,location,Option.map_some,Option.some.injEq] using represented
      rw [← equal]
      exact single_wellFormed q current
  | fork value left right ihl ihr =>
    obtain ⟨l,r,leftRep,rightRep,rfl⟩ := assemble_fork represented
    exact MultiSourceProgram.join_wellFormed [] l r (ihl l leftRep) (ihr r rightRep)

theorem assemble_congr (layout : Source C Unit) (before after : ProjectionForest.State C α ρ)
    (same : ∀ q ∈ colors layout, before q = after q) : assemble before layout = assemble after layout := by
  induction layout with
  | leaf q value => rw [assemble,assemble,same q (by simp [colors,Source.shape,RouterProjection.Router.leaves])]
  | fork value left right ihl ihr =>
    have leftSame : assemble before left = assemble after left := ihl (fun q member => same q (by
      change q ∈ left.shape.leaves++right.shape.leaves
      exact List.mem_append_left _ member))
    have rightSame : assemble before right = assemble after right := ihr (fun q member => same q (by
      change q ∈ left.shape.leaves++right.shape.leaves
      exact List.mem_append_right _ member))
    simp only [assemble,leftSame,rightSame]

theorem assemble_absent (forest : ProjectionForest.State C α ρ) (layout : Source C Unit)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble forest layout = some config)
    (q : C) (absent : forest q = none) : config.fingers q = none := by
  induction layout generalizing config with
  | leaf selected value =>
    cases location : forest selected with
    | none => simp only [assemble,location,Option.map_none,reduceCtorEq] at represented
    | some current =>
      have different : q ≠ selected := by intro equal; subst q; rw [location] at absent; cases absent
      have equal : single selected current = config := by simpa only [assemble,location,Option.map_some,Option.some.injEq] using represented
      rw [← equal]
      simp only [single,different,if_false]
  | fork value left right ihl ihr =>
    obtain ⟨l,r,leftRep,rightRep,rfl⟩ := assemble_fork represented
    simp only [MultiSourceProgram.join,ihl l leftRep,ihr r rightRep,Option.map_none]

theorem assemble_outside (forest : ProjectionForest.State C α ρ) (layout : Source C Unit)
    (config : MultiSourceProgram.Configuration C α (List ρ)) (represented : assemble forest layout = some config)
    (q : C) (missing : q ∉ colors layout) : config.fingers q = none := by
  induction layout generalizing config with
  | leaf selected value =>
    cases location : forest selected with
    | none => simp only [assemble,location,Option.map_none,reduceCtorEq] at represented
    | some current =>
      have different : q ≠ selected := by simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_singleton] using missing
      have equal : single selected current = config := by simpa only [assemble,location,Option.map_some,Option.some.injEq] using represented
      rw [← equal]
      simp only [single,different,if_false]
  | fork value left right ihl ihr =>
    obtain ⟨l,r,leftRep,rightRep,rfl⟩ := assemble_fork represented
    have neither : q ∉ colors left ∧ q ∉ colors right := by simpa only [colors,Source.shape,RouterProjection.Router.leaves,List.mem_append,not_or] using missing
    simp only [MultiSourceProgram.join,ihl l leftRep neither.1,ihr r rightRep neither.2,Option.map_none]

end ChaCha.Paper20261030.ForestConnector
