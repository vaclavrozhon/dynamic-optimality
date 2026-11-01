import TangoSquared.Paper20261030.MultiSourceComposition
import TangoSquared.Paper20261030.MultiSourceValidity

/-! Logical absence without clearing a physical finger. A presence bit
per register hides unused fingers from a source controller. A read of a
hidden register still costs one physical observation; its value is ignored.
Copies update both the physical pointer and its logical-presence bit.
This allows component entry to reuse a fixed set of physical registers.
-/

namespace TangoSquared.Paper20261030.MultiSourceProgram

open ColoredStorage SourcePointer SourcePositions

variable {α ρ F : Type*} [DecidableEq F]

def Configuration.mask (bits : F → Bool) (config : Configuration F α ρ) : Configuration F α ρ :=
  ⟨config.tree,fun finger => if bits finger then config.fingers finger else none⟩

theorem mask_present (bits : F → Bool) (config : Configuration F α ρ) (finger : F) (position : List Bool)
    (present : (config.mask bits).fingers finger = some position) :
    bits finger = true ∧ config.fingers finger = some position := by
  cases hb : bits finger <;> simp_all [Configuration.mask]

theorem mask_move (bits : F → Bool) (config : Configuration F α ρ) (finger : F) (action)
    (before after : Cursor α ρ) (used : bits finger = true) :
    (moveResult config finger action before after).mask bits = moveResult (config.mask bits) finger action before after := by
  simp only [Configuration.mask,moveResult]
  congr 1
  funext other
  by_cases same : other = finger
  · subst other; simp [used]
  · cases hb : bits other <;> simp [same,hb]

theorem mask_write (bits : F → Bool) (config : Configuration F α ρ) (current : Cursor α ρ) (fresh : ρ) :
    (writeResult config current fresh).mask bits = writeResult (config.mask bits) current fresh := rfl

theorem mask_copy (bits : F → Bool) (config : Configuration F α ρ) (destination origin : F) :
    (copyResult config destination origin).mask (Function.update bits destination (bits origin)) =
      copyResult (config.mask bits) destination origin := by
  simp only [Configuration.mask,copyResult]
  congr 1
  funext other
  by_cases same : other = destination
  · subst other; simp
  · simp [same]

end TangoSquared.Paper20261030.MultiSourceProgram

namespace TangoSquared.Paper20261030.MultiSourceMask

open ColoredStorage SourcePointer SourcePositions MultiSourceProgram

variable {α ρ F σ : Type*} [DecidableEq F]

abbrev State (σ F : Type*) := (F → Bool) × σ

def program (source : Program σ F ρ) : Program (State σ F) F ρ
  | (bits,state) => match source state with
    | .halt => .halt
    | .read finger next => .read finger (fun view => (bits,next (if bits finger then view else none)))
    | .nav finger action next => .nav finger action (bits,next)
    | .write finger fresh next => .write finger fresh (bits,next)
    | .copy destination origin next => .copy destination origin (Function.update bits destination (bits origin),next)

theorem compile_step {source : Program σ F ρ} {state next : σ}
    {before after : Configuration F α ρ} {entry}
    (step : Step source state before next after entry)
    (bits : F → Bool) (config : Configuration F α ρ) (valid : WellFormed config)
    (erases : config.mask bits = before) :
    ∃ newBits target observed, Step (program source) (bits,state) config (newBits,next) target observed ∧
      target.mask newBits = after := by
  subst before
  cases step with
  | @readNone finger next instruction absent =>
    cases hb : bits finger
    · cases hf : config.fingers finger with
      | none =>
        refine ⟨bits,config,none,?_,rfl⟩
        simpa only [hb,if_false,Bool.false_eq_true] using
          (Step.readNone (program := program source) (state := (bits,state))
            (next := fun view => (bits,next (if bits finger then view else none)))
            (by simp only [program,instruction]) hf)
      | some position =>
        obtain ⟨current,reached⟩ := valid finger position hf
        refine ⟨bits,config,some (finger,current.focus.rootRecord),?_,rfl⟩
        simpa only [hb,if_false,Bool.false_eq_true] using
          (Step.readSome (program := program source) (state := (bits,state))
            (next := fun view => (bits,next (if bits finger then view else none)))
            (by simp only [program,instruction]) hf reached)
    · have actual : config.fingers finger = none := by simpa only [Configuration.mask,hb,if_true] using absent
      refine ⟨bits,config,none,?_,rfl⟩
      simpa only [hb,if_true] using
        (Step.readNone (program := program source) (state := (bits,state))
          (next := fun view => (bits,next (if bits finger then view else none)))
          (by simp only [program,instruction]) actual)
  | @readSome finger position current next instruction present reached =>
    obtain ⟨used,actual⟩ := mask_present bits config finger position present
    refine ⟨bits,config,some (finger,current.focus.rootRecord),?_,rfl⟩
    simpa only [used,if_true] using
      (Step.readSome (program := program source) (state := (bits,state))
        (next := fun view => (bits,next (if bits finger then view else none)))
        (by simp only [program,instruction]) actual reached)
  | @nav finger position current target action next instruction present reached moved =>
    obtain ⟨used,actual⟩ := mask_present bits config finger position present
    exact ⟨bits,_,none,Step.nav (by simp only [program,instruction]) actual reached moved,
      mask_move bits config finger action current target used⟩
  | @write finger position current fresh next instruction present reached =>
    obtain ⟨used,actual⟩ := mask_present bits config finger position present
    exact ⟨bits,_,none,Step.write (by simp only [program,instruction]) actual reached,rfl⟩
  | @copy destination origin next instruction =>
    exact ⟨Function.update bits destination (bits origin),_,none,
      Step.copy (by simp only [program,instruction]),mask_copy bits config destination origin⟩

theorem compile_run {source : Program σ F ρ} {state last : σ}
    {before after : Configuration F α ρ} {reads cost}
    (run : Run source state before last after reads cost)
    (bits : F → Bool) (config : Configuration F α ρ) (valid : WellFormed config)
    (erases : config.mask bits = before) :
    ∃ newBits target actualReads, Run (program source) (bits,state) config (newBits,last) target actualReads cost ∧
      target.mask newBits = after ∧ WellFormed target := by
  induction run generalizing bits config with
  | halt stopped => exact ⟨bits,config,[],.halt (by simp only [program,stopped]),erases,valid⟩
  | next first rest ih =>
    obtain ⟨middleBits,middle,entry,firstRun,middleRep⟩ := compile_step first bits config valid erases
    obtain ⟨finalBits,target,entries,restRun,targetRep,targetValid⟩ := ih middleBits middle (firstRun.wellFormed valid) middleRep
    exact ⟨finalBits,target,_,.next firstRun restRun,targetRep,targetValid⟩

end TangoSquared.Paper20261030.MultiSourceMask
