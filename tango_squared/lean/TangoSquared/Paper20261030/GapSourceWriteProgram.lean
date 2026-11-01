import TangoSquared.Paper20261030.GapSourceProgramLayout

/-! The local compiler's record updates. A read obtains the key and the
unchanged fields at the actual node; a subsequent write changes only the
requested cached size or application value and retains the core marker. -/

namespace TangoSquared.Paper20261030.GapSource.Controller

open ColoredStorage SourcePointer SourceLocalProgram Auxiliary DynamicOptimality MTR

variable {α κ ρ : Type*}

inductive Update (ρ : Type*) where
  | value (fresh : ρ)
  | size (fresh : Nat)

def Update.apply (operation : Update ρ) (entry : Record κ ρ) : Record κ ρ :=
  match operation with
  | .value fresh => (entry.1,⟨entry.2.1,fresh⟩)
  | .size fresh => (fresh,entry.2)

inductive WriteState (κ ρ : Type*) where
  | start (operation : Update ρ)
  | write (entry : MarkedRecord κ ρ)
  | done

def writeProgram : Program (WriteState κ ρ) (MarkedRecord κ ρ)
  | .start operation => .read (fun entry _ => .write (mark (operation.apply (unmark entry))))
  | .write entry => .write entry .done
  | .done => .halt

theorem write_fork (operation : Update ρ) (entry : Record κ ρ)
    (left right : Source α (MarkedRecord κ ρ)) (outside) :
    Run writeProgram (.start operation) ⟨.fork (mark entry) left right,outside⟩ .done
      ⟨.fork (mark (operation.apply entry)) left right,outside⟩ [mark entry] 2 := by
  have read : Step writeProgram (.start operation) ⟨.fork (mark entry) left right,outside⟩
      (.write (mark (operation.apply entry))) ⟨.fork (mark entry) left right,outside⟩ (some (mark entry)) := by
    have basic : Step writeProgram (.start operation) ⟨.fork (mark entry) left right,outside⟩
        (.write (mark (operation.apply (unmark (mark entry)))))
        ⟨.fork (mark entry) left right,outside⟩ (some (mark entry)) := by
      apply Step.read (next := fun (value : MarkedRecord κ ρ) (_ : Bool) =>
        WriteState.write (mark (operation.apply (unmark value))))
      rfl
    simpa only [unmark_mark] using basic
  have write : Step writeProgram (.write (mark (operation.apply entry)))
      ⟨.fork (mark entry) left right,outside⟩ .done
      ⟨.fork (mark (operation.apply entry)) left right,outside⟩ none := .write rfl
  exact .next read (.next write (.halt rfl))

theorem write_cursor (ports : Nat → Source α (MarkedRecord κ ρ)) (base : Nat) (operation : Update ρ)
    (left right : RawTree (Record κ ρ)) (entry : Record κ ρ) (rest : List (Pointer.Frame (Record κ ρ))) :
    ∃ reads, Run writeProgram (.start operation)
      (encodedCursor ports base ⟨.node left entry right,rest⟩) .done
      (encodedCursor ports base ⟨.node left (operation.apply entry) right,rest⟩) reads 2 := by
  have run := write_fork operation entry
    (GapSource.encode (Relabel.tree mark left) ports (base+PointerGraft.offset (rest.map (Relabel.frame mark))))
    (GapSource.encode (Relabel.tree mark right) ports
      (base+PointerGraft.offset (rest.map (Relabel.frame mark))+(Relabel.tree mark left).size+1))
    (GapSource.frames ports base (Relabel.tree mark (.node left entry right)).size (rest.map (Relabel.frame mark)))
  exact ⟨_,run⟩

end TangoSquared.Paper20261030.GapSource.Controller
