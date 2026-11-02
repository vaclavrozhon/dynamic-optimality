import ChaCha.Paper20261030.StructuralRotationReads
import ChaCha.Paper20261030.SourceProgramComposition

/-! The structural rotation kernel as a fixed local program. Its only
inputs are the direction and the identifier function. It reads both
pivots, computes their new descriptors, and repairs the middle subtree's
parent field. Neither a subtree nor an execution trace is a program input.
The external parent's child descriptor is handled by the context repair.
-/

namespace ChaCha.Paper20261030.Structural

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι C : Type*} [DecidableEq C]

def leftPivotRecords (identifier : ρ → ι) (oldP oldQ : ρ × Fields ι C) :
    Option ((ρ × Fields ι C) × (ρ × Fields ι C)) :=
  match oldP.2.children,oldQ.2.children with
  | some (u,_),some (v,w) =>
      let newP := (oldP.1,Fields.mk (some (identifier oldQ.1)) (u.colors ∪ v.colors) (some (u,v)))
      let newQ := (oldQ.1,Fields.mk oldP.2.parent oldP.2.colors
        (some (Child.mk (identifier oldP.1) newP.2.colors,w)))
      some (newQ,newP)
  | _,_ => none

theorem leftPivotRecords_exact (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) :
    leftPivotRecords identifier
      (annotate identifier color parent (.fork p u (.fork q v w))).rootRecord
      (annotate identifier color (some (identifier p)) (.fork q v w)).rootRecord =
      some ((annotate identifier color parent (.fork q (.fork p u v) w)).rootRecord,
        (annotate identifier color (some (identifier q)) (.fork p u v)).rootRecord) := by
  simp only [annotate,Source.rootRecord,leftPivotRecords,fields,descriptor,Source.support,Finset.union_assoc]

namespace RotationController

inductive State (ρ ι C : Type*) where
  | start
  | goPivot (old : ρ × Fields ι C)
  | readPivot (old : ρ × Fields ι C)
  | goRoot (root child : ρ × Fields ι C)
  | rotate (root child : ρ × Fields ι C)
  | writeRoot (root child : ρ × Fields ι C)
  | goChild (child : ρ × Fields ι C)
  | writeChild (child : ρ × Fields ι C)
  | goMiddle (parent : ι)
  | readMiddle (parent : ι)
  | writeMiddle (record : ρ × Fields ι C)
  | upMiddle
  | upRoot
  | done
  | error

def pivots (identifier : ρ → ι) (right : Bool) (old other : ρ × Fields ι C) : State ρ ι C :=
  match (if right then rightPivotRecords identifier else leftPivotRecords identifier) old other with
  | some (root,child) => .goRoot root child
  | none => .error

def program (identifier : ρ → ι) (right : Bool) : Program (State ρ ι C) (ρ × Fields ι C)
  | .start => .read (fun record _ => .goPivot record)
  | .goPivot old => .nav (if right then .left else .right) (.readPivot old)
  | .readPivot old => .read (fun record _ => pivots identifier right old record)
  | .goRoot root child => .nav .up (.rotate root child)
  | .rotate root child => .nav (if right then .rotateRight else .rotateLeft) (.writeRoot root child)
  | .writeRoot root child => .write root (.goChild child)
  | .goChild child => .nav (if right then .right else .left) (.writeChild child)
  | .writeChild child => .write child (.goMiddle (identifier child.1))
  | .goMiddle parent => .nav (if right then .left else .right) (.readMiddle parent)
  | .readMiddle parent => .read (fun record _ => .writeMiddle (reparent (some parent) record))
  | .writeMiddle record => .write record .upMiddle
  | .upMiddle => .nav .up .upRoot
  | .upRoot => .nav .up .done
  | .done | .error => .halt

theorem rotate_right (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) (outside) :
    ∃ reads, Run (program identifier true) .start
      ⟨annotate identifier color parent (.fork q (.fork p u v) w),outside⟩ .done
      ⟨annotate identifier color parent (.fork p u (.fork q v w)),outside⟩ reads 13 := by
  let U := annotate identifier color (some (identifier p)) u
  let V := annotate identifier color (some (identifier p)) v
  let W := annotate identifier color (some (identifier q)) w
  let V' := annotate identifier color (some (identifier q)) v
  let oldP := (annotate identifier color (some (identifier q)) (.fork p u v)).rootRecord
  let oldQ := (annotate identifier color parent (.fork q (.fork p u v) w)).rootRecord
  let newP := (annotate identifier color parent (.fork p u (.fork q v w))).rootRecord
  let newQ := (annotate identifier color (some (identifier p)) (.fork q v w)).rootRecord
  have pivot : pivots identifier true oldQ oldP = .goRoot newP newQ := by
    simp only [pivots,ite_true,oldQ,oldP,rightPivotRecords_exact,newP,newQ]
  have middle : V.setRoot (reparent (some (identifier q)) V.rootRecord) = V' := by
    rw [reparent_root,annotate_root]
    exact (annotate_parent identifier color (some (identifier p)) (some (identifier q)) v).symm
  have readPivot : SourceLocalProgram.Step (program identifier true) (.readPivot oldQ)
      ⟨.fork oldP U V,.left oldQ W::outside⟩ (.goRoot newP newQ)
      ⟨.fork oldP U V,.left oldQ W::outside⟩ (some oldP) := by
    have actual := SourceLocalProgram.Step.read (α := α)
      (cursor := (⟨.fork oldP U V,.left oldQ W::outside⟩ : Cursor α (ρ × Fields ι C)))
      (program := program identifier true) (state := .readPivot oldQ)
      (next := fun record _ => pivots identifier true oldQ record) rfl
    simpa only [Source.rootRecord,pivot] using actual
  have finish : Run (program identifier true) .upMiddle
      ⟨V',.left newQ W::.right U newP::outside⟩ .done
      ⟨.fork newP U (.fork newQ V' W),outside⟩ [] 2 :=
    Run.next (program := program identifier true) (.nav rfl rfl)
      (Run.next (program := program identifier true) (.nav rfl rfl) (.halt rfl))
  have writeMiddle : Run (program identifier true)
      (.writeMiddle (reparent (some (identifier q)) V.rootRecord))
      ⟨V,.left newQ W::.right U newP::outside⟩ .done
      ⟨.fork newP U (.fork newQ V' W),outside⟩ [] 3 := by
    apply Run.next (program := program identifier true) (.write rfl)
    simpa only [middle] using finish
  refine ⟨[oldQ,oldP,V.rootRecord],?_⟩
  change Run (program identifier true) .start ⟨.fork oldQ (.fork oldP U V) W,outside⟩ .done
    ⟨.fork newP U (.fork newQ V' W),outside⟩ [oldQ,oldP,V.rootRecord] 13
  exact Run.next (program := program identifier true) (.read rfl) (Run.next (program := program identifier true) (.nav rfl rfl) (Run.next (program := program identifier true) readPivot
    (Run.next (program := program identifier true) (.nav rfl rfl) (Run.next (program := program identifier true) (.nav rfl rfl) (Run.next (program := program identifier true) (.write rfl)
      (Run.next (program := program identifier true) (.nav rfl rfl) (Run.next (program := program identifier true) (.write rfl) (Run.next (program := program identifier true) (.nav rfl rfl)
        (Run.next (program := program identifier true) (.read rfl) writeMiddle)))))))))

theorem rotate_left (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (u v w : Source α ρ) (p q : ρ) (outside) :
    ∃ reads, Run (program identifier false) .start
      ⟨annotate identifier color parent (.fork p u (.fork q v w)),outside⟩ .done
      ⟨annotate identifier color parent (.fork q (.fork p u v) w),outside⟩ reads 13 := by
  let U := annotate identifier color (some (identifier p)) u
  let V := annotate identifier color (some (identifier q)) v
  let W := annotate identifier color (some (identifier q)) w
  let V' := annotate identifier color (some (identifier p)) v
  let oldP := (annotate identifier color parent (.fork p u (.fork q v w))).rootRecord
  let oldQ := (annotate identifier color (some (identifier p)) (.fork q v w)).rootRecord
  let newP := (annotate identifier color (some (identifier q)) (.fork p u v)).rootRecord
  let newQ := (annotate identifier color parent (.fork q (.fork p u v) w)).rootRecord
  have pivot : pivots identifier false oldP oldQ = .goRoot newQ newP := by
    simp only [pivots,Bool.false_eq_true,ite_false,oldP,oldQ,leftPivotRecords_exact,newP,newQ]
  have middle : V.setRoot (reparent (some (identifier p)) V.rootRecord) = V' := by
    rw [reparent_root,annotate_root]
    exact (annotate_parent identifier color (some (identifier q)) (some (identifier p)) v).symm
  have readPivot : SourceLocalProgram.Step (program identifier false) (.readPivot oldP)
      ⟨.fork oldQ V W,.right U oldP::outside⟩ (.goRoot newQ newP)
      ⟨.fork oldQ V W,.right U oldP::outside⟩ (some oldQ) := by
    have actual := SourceLocalProgram.Step.read (α := α)
      (cursor := (⟨.fork oldQ V W,.right U oldP::outside⟩ : Cursor α (ρ × Fields ι C)))
      (program := program identifier false) (state := .readPivot oldP)
      (next := fun record _ => pivots identifier false oldP record) rfl
    simpa only [Source.rootRecord,pivot] using actual
  have finish : Run (program identifier false) .upMiddle
      ⟨V',.right U newP::.left newQ W::outside⟩ .done
      ⟨.fork newQ (.fork newP U V') W,outside⟩ [] 2 :=
    Run.next (program := program identifier false) (.nav rfl rfl)
      (Run.next (program := program identifier false) (.nav rfl rfl) (.halt rfl))
  have writeMiddle : Run (program identifier false)
      (.writeMiddle (reparent (some (identifier p)) V.rootRecord))
      ⟨V,.right U newP::.left newQ W::outside⟩ .done
      ⟨.fork newQ (.fork newP U V') W,outside⟩ [] 3 := by
    apply Run.next (program := program identifier false) (.write rfl)
    simpa only [middle] using finish
  refine ⟨[oldP,oldQ,V.rootRecord],?_⟩
  change Run (program identifier false) .start ⟨.fork oldP U (.fork oldQ V W),outside⟩ .done
    ⟨.fork newQ (.fork newP U V') W,outside⟩ [oldP,oldQ,V.rootRecord] 13
  exact Run.next (program := program identifier false) (.read rfl) (Run.next (program := program identifier false) (.nav rfl rfl) (Run.next (program := program identifier false) readPivot
    (Run.next (program := program identifier false) (.nav rfl rfl) (Run.next (program := program identifier false) (.nav rfl rfl) (Run.next (program := program identifier false) (.write rfl)
      (Run.next (program := program identifier false) (.nav rfl rfl) (Run.next (program := program identifier false) (.write rfl) (Run.next (program := program identifier false) (.nav rfl rfl)
        (Run.next (program := program identifier false) (.read rfl) writeMiddle)))))))))

/-- The controller stores at most two full annotated records. The only
other data are a program counter and, during the middle repair, one id. -/
def workingRecords : State ρ ι C → Nat
  | .start | .goMiddle _ | .readMiddle _ | .upMiddle | .upRoot | .done | .error => 0
  | .goPivot _ | .readPivot _ | .goChild _ | .writeChild _ | .writeMiddle _ => 1
  | .goRoot _ _ | .rotate _ _ | .writeRoot _ _ => 2

omit [DecidableEq C] in
theorem working_records (state : State ρ ι C) : workingRecords state ≤ 2 := by
  cases state <;> simp only [workingRecords] <;> omega

end RotationController
end ChaCha.Paper20261030.Structural
