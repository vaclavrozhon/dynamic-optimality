import ChaCha.Paper20261030.LocalPacketPrefixResume
import ChaCha.Paper20261030.MultiSourceStationaryFingers
import ChaCha.Paper20261030.MultiSourceService

set_option autoImplicit false

/-!
# Carrying enclosing packets across a multifinger component operation

The entry finger reads and strips the enclosing prefix. The component
controller then runs with all its ordinary registers. Its scalar final
state selects the return finger, which moves up the known connector
depth and restores the saved prefix using the newly read physical id.
All other fingers retain their positions from the end of the component
operation. Parent child-descriptor repair is a subsequent operation.
-/

namespace ChaCha.Paper20261030.MultiSourcePacketPrefix

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram PhysicalPacketStaging PacketLayers

variable {α β ρ ι F σ : Type*} [DecidableEq F]

inductive State (σ α ρ ι : Type*) where
  | start
  | strip (saved : Packet α ρ ι) (fresh : Context.Cell α ρ ι)
  | running (saved : Packet α ρ ι) (oldId : ι) (phase : σ)
  | returning (saved : Packet α ρ ι) (oldId : ι) (last : σ) (phase : Option (PacketPrefixResume.State α ρ ι))
  | blocked

def enter (kernel : Program σ F (Context.Cell α ρ ι)) (levels : Nat)
    (saved : Packet α ρ ι) (oldId : ι) (phase : σ) : State σ α ρ ι :=
  match kernel phase with
  | .halt => .returning saved oldId phase (some (PacketPrefixResume.ascend levels))
  | _ => .running saved oldId phase

def program (entry : F) (exit : σ → F) (count levels : Nat)
    (kernel : Program σ F (Context.Cell α ρ ι)) (initial : σ) :
    Program (State σ α ρ ι) F (Context.Cell α ρ ι)
  | .start => .read entry (fun observed => match observed with
      | none => .blocked
      | some (record,_) => .strip (record.2.take count) (record.1,record.2.drop count))
  | .strip saved fresh => .write entry fresh (enter kernel levels saved fresh.1 initial)
  | .running saved oldId phase => (kernel phase).mapState (enter kernel levels saved oldId)
  | .returning saved oldId last phase =>
      (MultiSourceSingleCursor.program (PacketPrefixResume.program saved) (exit last) phase).mapState
        (.returning saved oldId last)
  | .blocked => .halt

theorem enter_code (entry : F) (exit : σ → F) (count levels : Nat)
    (kernel : Program σ F (Context.Cell α ρ ι)) (initial : σ)
    (saved : Packet α ρ ι) (oldId : ι) (phase : σ) (active : kernel phase ≠ .halt) :
    program entry exit count levels kernel initial (enter kernel levels saved oldId phase) =
      (kernel phase).mapState (enter kernel levels saved oldId) := by
  cases code : kernel phase <;> simp_all [enter,program]

theorem resume_edgeOnly (saved : Packet α ρ ι) :
    MultiSourceSingleCursor.EdgeOnly (PacketPrefixResume.program saved) := by
  intro state move next code
  cases state with
  | ascending remaining =>
    simp only [PacketPrefixResume.program,SourceLocalProgram.Instruction.nav.injEq] at code
    cases code.1
    trivial
  | reading | writing | done => simp only [PacketPrefixResume.program,reduceCtorEq] at code

def attached (saved : Packet α ρ ι) (focus : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι)))
    (config : Configuration F β (Context.Cell α ρ ι)) : Configuration F β (Context.Cell α ρ ι) :=
  ⟨plug (PacketPrefixTransfer.attach saved focus) outside,config.fingers⟩

theorem attached_wellFormed (saved : Packet α ρ ι) (focus : Source β (Context.Cell α ρ ι))
    (outside : List (Frame β (Context.Cell α ρ ι)))
    (config : Configuration F β (Context.Cell α ρ ι)) (tree : config.tree = plug focus outside)
    (valid : WellFormed config) : WellFormed (attached saved focus outside config) :=
  write_wellFormed config valid ⟨focus,outside⟩ tree.symm (focus.rootRecord.1,saved++focus.rootRecord.2)

theorem execute (entry : F) (exit : σ → F) (saved : Packet α ρ ι)
    (kernel : Program σ F (Context.Cell α ρ ι)) (initial last : σ)
    (before after : Configuration F β (Context.Cell α ρ ι)) {reads cost}
    (body : Run kernel initial before last after reads cost)
    (focus finalFocus : Source β (Context.Cell α ρ ι))
    (outside inside finalOutside : List (Frame β (Context.Cell α ρ ι)))
    (entryRep : MultiSourceSingleCursor.Represents entry ⟨focus,outside⟩ before)
    (exitRep : MultiSourceSingleCursor.Represents (exit last) ⟨finalFocus,inside++finalOutside⟩ after) :
    ∃ target observed,
      Run (program entry exit saved.length inside.length kernel initial) .start
        (attached saved focus outside before)
        (.returning saved focus.rootRecord.1 last (some (.done (plug finalFocus inside).rootRecord.1)))
        target observed (cost+inside.length+4) ∧
      MultiSourceSingleCursor.Represents (exit last)
        ⟨PacketPrefixTransfer.output saved (plug finalFocus inside),finalOutside⟩ target ∧
      (∀ other, other ≠ exit last → target.fingers other = after.fingers other) := by
  let code := program entry exit saved.length inside.length kernel initial
  let input := attached saved focus outside before
  let entered := PacketPrefixTransfer.attach saved focus
  have enteredRoot : entered.rootRecord = (focus.rootRecord.1,saved++focus.rootRecord.2) := by
    cases focus <;> rfl
  have stripped : entered.setRoot focus.rootRecord = focus := by cases focus <;> rfl
  have found : locate input.tree (address (⟨entered,outside⟩ : Cursor β (Context.Cell α ρ ι))) =
      some ⟨entered,outside⟩ := locate_cursor ⟨entered,outside⟩
  have present : input.fingers entry = some (address (⟨entered,outside⟩ : Cursor β (Context.Cell α ρ ι))) := entryRep.2
  have first : Step code .start input (.strip saved focus.rootRecord) input (some (entry,entered.rootRecord)) := by
    have actual := Step.readSome (program := code) (state := .start) (config := input)
      (current := ⟨entered,outside⟩)
      (next := fun observed => match observed with
        | none => State.blocked
        | some (record,_) => State.strip (record.2.take saved.length) (record.1,record.2.drop saved.length))
      rfl present found
    simpa only [enteredRoot,List.take_left,List.drop_left,Prod.mk.eta] using actual
  have written : writeResult input ⟨entered,outside⟩ focus.rootRecord = before := by
    change Configuration.mk (plug (entered.setRoot focus.rootRecord) outside) before.fingers = before
    have tree : before.tree = plug focus outside := entryRep.1
    rw [stripped,← tree]
  have strip : Step code (.strip saved focus.rootRecord) input
      (enter kernel inside.length saved focus.rootRecord.1 initial) before none := by
    rw [← written]
    exact Step.write rfl present found
  have front := body.map_prefix (target := code) (enter kernel inside.length saved focus.rootRecord.1)
    (enter_code entry exit saved.length inside.length kernel initial saved focus.rootRecord.1)
  have boundary : enter kernel inside.length saved focus.rootRecord.1 last =
      .returning saved focus.rootRecord.1 last (some (PacketPrefixResume.ascend inside.length)) := by
    simp only [enter,body.halted]
  rw [boundary] at front
  obtain ⟨target,rest,targetRep,others⟩ := MultiSourceSingleCursor.compile_edge_run
    (PacketPrefixResume.program saved) (resume_edgeOnly saved) (exit last)
    (PacketPrefixResume.run saved finalFocus inside finalOutside) after exitRep
  have back := rest.map_prefix (target := code) (State.returning saved focus.rootRecord.1 last) (fun _ _ => rfl)
  have all := ((first.prefix.append strip.prefix).append front).append back
  have actual := all.run rfl
  have sum : 1+1+cost+(inside.length+2) = cost+inside.length+4 := by omega
  rw [sum] at actual
  exact ⟨target,_,actual,targetRep,others⟩

end ChaCha.Paper20261030.MultiSourcePacketPrefix
