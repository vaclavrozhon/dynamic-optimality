import ChaCha.Paper20261030.LocalStructuralContext

/-! Payload writes with maintained structural fields, including writes
that change the record's identifier. The two child roots, when present,
are reached and their parent fields are read and rewritten. The kernel
uses at most ten commands; the context wrapper repairs the external parent.
-/

namespace ChaCha.Paper20261030.Structural

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι C : Type*} [DecidableEq C]

theorem fields_setRoot (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (source : Source α ρ) (fresh : ρ) :
    fields identifier color parent (source.setRoot fresh) = fields identifier color parent source := by
  cases source <;> rfl

namespace WriteController

inductive State (ρ ι C : Type*) where
  | start
  | writeRoot (record : ρ × Fields ι C) (leaf : Bool)
  | goLeft
  | readLeft
  | writeLeft (record : ρ × Fields ι C)
  | upLeft
  | goRight
  | readRight
  | writeRight (record : ρ × Fields ι C)
  | upRight
  | done

def program (identifier : ρ → ι) (fresh : ρ) : Program (State ρ ι C) (ρ × Fields ι C)
  | .start => .read (fun record leaf => .writeRoot (fresh,record.2) leaf)
  | .writeRoot record leaf => .write record (if leaf then .done else .goLeft)
  | .goLeft => .nav .left .readLeft
  | .readLeft => .read (fun record _ => .writeLeft (reparent (some (identifier fresh)) record))
  | .writeLeft record => .write record .upLeft
  | .upLeft => .nav .up .goRight
  | .goRight => .nav .right .readRight
  | .readRight => .read (fun record _ => .writeRight (reparent (some (identifier fresh)) record))
  | .writeRight record => .write record .upRight
  | .upRight => .nav .up .done
  | .done => .halt

theorem write (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (source : Source α ρ) (fresh : ρ) (outside) :
    ∃ reads cost, Run (program identifier fresh) .start ⟨annotate identifier color parent source,outside⟩
      .done ⟨annotate identifier color parent (source.setRoot fresh),outside⟩ reads cost ∧ cost ≤ 10 := by
  cases source with
  | leaf key old =>
    refine ⟨[(annotate identifier color parent (.leaf key old)).rootRecord],2,?_,by decide⟩
    exact Run.next (program := program identifier fresh) (.read rfl)
      (Run.next (program := program identifier fresh) (.write rfl) (.halt rfl))
  | fork old l r =>
    let L := annotate identifier color (some (identifier old)) l
    let R := annotate identifier color (some (identifier old)) r
    let L' := annotate identifier color (some (identifier fresh)) l
    let R' := annotate identifier color (some (identifier fresh)) r
    let oldRoot := (old,fields identifier color parent (.fork old l r))
    let newRoot := (fresh,fields identifier color parent (.fork fresh l r))
    let code := program (C := C) identifier fresh
    have leftRoot : L.setRoot (reparent (some (identifier fresh)) L.rootRecord) = L' := by
      rw [reparent_root,annotate_root]
      exact (annotate_parent identifier color (some (identifier old)) (some (identifier fresh)) l).symm
    have rightRoot : R.setRoot (reparent (some (identifier fresh)) R.rootRecord) = R' := by
      rw [reparent_root,annotate_root]
      exact (annotate_parent identifier color (some (identifier old)) (some (identifier fresh)) r).symm
    have finish : Run code .upRight ⟨R',.right L' newRoot::outside⟩ .done
        ⟨.fork newRoot L' R',outside⟩ [] 1 :=
      Run.next (program := code) (.nav rfl rfl) (.halt rfl)
    have rightWrite : Run code (.writeRight (reparent (some (identifier fresh)) R.rootRecord))
        ⟨R,.right L' newRoot::outside⟩ .done ⟨.fork newRoot L' R',outside⟩ [] 2 := by
      apply Run.next (program := code) (.write rfl)
      simpa only [rightRoot] using finish
    have rightRun : Run code .upLeft ⟨L',.left newRoot R::outside⟩ .done
        ⟨.fork newRoot L' R',outside⟩ [R.rootRecord] 5 :=
      Run.next (program := code) (.nav rfl rfl)
        (Run.next (program := code) (.nav rfl rfl)
          (Run.next (program := code) (.read rfl) rightWrite))
    have leftWrite : Run code (.writeLeft (reparent (some (identifier fresh)) L.rootRecord))
        ⟨L,.left newRoot R::outside⟩ .done ⟨.fork newRoot L' R',outside⟩ [R.rootRecord] 6 := by
      apply Run.next (program := code) (.write rfl)
      simpa only [leftRoot] using rightRun
    refine ⟨[oldRoot,L.rootRecord,R.rootRecord],10,?_,le_rfl⟩
    change Run code .start ⟨.fork oldRoot L R,outside⟩ .done
      ⟨.fork newRoot L' R',outside⟩ [oldRoot,L.rootRecord,R.rootRecord] 10
    exact Run.next (program := code) (.read rfl)
      (Run.next (program := code) (.write rfl)
        (Run.next (program := code) (.nav rfl rfl)
          (Run.next (program := code) (.read rfl) leftWrite)))

theorem write_cursor [DecidableEq ι] (identifier : ρ → ι) (color : α → C)
    (source : Source α ρ) (fresh : ρ) (outside : List (Frame α ρ))
    (unique : ((plug source outside).inventory identifier).Nodup) :
    ∃ reads cost, Run (ContextController.program identifier (program identifier fresh) .start) .start
      (cursor identifier color ⟨source,outside⟩) .done
      (cursor identifier color ⟨source.setRoot fresh,outside⟩) reads cost ∧ cost ≤ 16 := by
  obtain ⟨reads,cost,body,bounded⟩ := write identifier color (parentId identifier outside)
    source fresh (frames identifier color source outside)
  obtain ⟨allReads,allCost,actual,total⟩ := ContextController.lift identifier color
    (program identifier fresh) .start .done source (source.setRoot fresh) outside
    (by cases source <;> rfl) unique body rfl
  exact ⟨allReads,allCost,actual,by omega⟩

end WriteController
end ChaCha.Paper20261030.Structural
