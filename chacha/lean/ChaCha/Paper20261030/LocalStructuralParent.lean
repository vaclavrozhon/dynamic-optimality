import ChaCha.Paper20261030.StructuralCursor
import ChaCha.Paper20261030.SourceProgramComposition

/-! Repairing the external parent's child descriptor with four local
commands. The old identifier determines the return direction from the
parent record that is actually read. Identifiers are compared as values;
they are never converted into pointers. Unique identifiers in the initial
tree justify the direction test, including at an arbitrary cursor depth.
-/

namespace ChaCha.Paper20261030.Structural

open ColoredStorage SourcePointer SourceLocalProgram

variable {α ρ ι C : Type*} [DecidableEq C]

theorem root_mem_inventory (identifier : ρ → ι) (source : Source α ρ) :
    identifier source.rootRecord ∈ source.inventory identifier := by
  cases source <;> simp [Source.rootRecord]

theorem inventory_le_plug (identifier : ρ → ι) (source : Source α ρ)
    (outside : List (Frame α ρ)) :
    source.inventory identifier ≤ (plug source outside).inventory identifier := by
  induction outside generalizing source with
  | nil => exact le_rfl
  | cons frame rest ih =>
    cases frame with
    | left record sibling =>
      exact (show source.inventory identifier ≤ (Source.fork record source sibling).inventory identifier by
        simp only [Source.inventory_fork]; exact (le_add_of_nonneg_left zero_le).trans
          (le_add_of_nonneg_right zero_le)).trans (ih _)
    | right sibling record =>
      exact (show source.inventory identifier ≤ (Source.fork record sibling source).inventory identifier by
        simp only [Source.inventory_fork]; exact le_add_of_nonneg_left zero_le).trans (ih _)

theorem child_ids_distinct (identifier : ρ → ι) (record : ρ) (left right : Source α ρ)
    (unique : ((Source.fork record left right).inventory identifier).Nodup) :
    identifier left.rootRecord ≠ identifier right.rootRecord := by
  simp only [Source.inventory_fork,Multiset.nodup_add] at unique
  have separate : Disjoint (left.inventory identifier) (right.inventory identifier) :=
    (Multiset.disjoint_add_left.mp unique.2.2).2
  intro equal
  exact (Multiset.disjoint_left.mp separate) (root_mem_inventory identifier left)
    (equal ▸ root_mem_inventory identifier right)

namespace ParentController

variable [DecidableEq ι]

inductive State (ρ ι C : Type*) where
  | goUp
  | readParent
  | writeParent (record : ρ × Fields ι C) (left : Bool)
  | goDown (left : Bool)
  | done
  | error

def initial : Option ι → State ρ ι C
  | none => .done
  | some _ => .goUp

def replaceChild (old : ι) (fresh : Child ι C) (record : ρ × Fields ι C) : State ρ ι C :=
  match record.2.children with
  | none => .error
  | some (l,r) =>
      if l.id = old then .writeParent (record.1,{record.2 with children := some (fresh,r)}) true
      else .writeParent (record.1,{record.2 with children := some (l,fresh)}) false

def program (old : ι) (fresh : Child ι C) : Program (State ρ ι C) (ρ × Fields ι C)
  | .goUp => .nav .up .readParent
  | .readParent => .read (fun record _ => replaceChild old fresh record)
  | .writeParent record left => .write record (.goDown left)
  | .goDown left => .nav (if left then .left else .right) .done
  | .done | .error => .halt

theorem replace_left (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (record : ρ) (before after sibling : Source α ρ)
    (sameColors : before.support color = after.support color) :
    replaceChild (identifier before.rootRecord) (descriptor identifier color after)
      (record,fields identifier color parent (.fork record before sibling)) =
      .writeParent (record,fields identifier color parent (.fork record after sibling)) true := by
  simp only [replaceChild,fields,descriptor,Source.support,ite_true,sameColors]

theorem replace_right (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (record : ρ) (before after sibling : Source α ρ)
    (sameColors : before.support color = after.support color)
    (distinct : identifier sibling.rootRecord ≠ identifier before.rootRecord) :
    replaceChild (identifier before.rootRecord) (descriptor identifier color after)
      (record,fields identifier color parent (.fork record sibling before)) =
      .writeParent (record,fields identifier color parent (.fork record sibling after)) false := by
  simp only [replaceChild,fields,descriptor,Source.support,distinct,ite_false,sameColors]

theorem repair (identifier : ρ → ι) (color : α → C) (before after : Source α ρ)
    (sameColors : before.support color = after.support color) (outside : List (Frame α ρ))
    (unique : ((plug before outside).inventory identifier).Nodup) :
    ∃ reads cost,
      Run (program (identifier before.rootRecord) (descriptor identifier color after))
        (initial (parentId identifier outside))
        ⟨annotate identifier color (parentId identifier outside) after,frames identifier color before outside⟩
        .done (cursor identifier color ⟨after,outside⟩) reads cost ∧ cost ≤ 4 := by
  cases outside with
  | nil => exact ⟨[],0,.halt rfl,by decide⟩
  | cons frame rest =>
    cases frame with
    | left record sibling =>
      let A := annotate identifier color (some (identifier record)) after
      let R := annotate identifier color (some (identifier record)) sibling
      let old := (record,fields identifier color (parentId identifier rest) (.fork record before sibling))
      let fresh := (record,fields identifier color (parentId identifier rest) (.fork record after sibling))
      have tail := frames_congr identifier color (before := .fork record before sibling)
        (after := .fork record after sibling) rfl (by simp only [Source.support,sameColors]) rest
      let rest' := frames identifier color (.fork record after sibling) rest
      let code := program (ρ := ρ) (identifier before.rootRecord) (descriptor identifier color after)
      have read : SourceLocalProgram.Step code .readParent ⟨.fork old A R,rest'⟩
          (.writeParent fresh true) ⟨.fork old A R,rest'⟩ (some old) := by
        have actual := SourceLocalProgram.Step.read (program := code) (state := .readParent)
          (cursor := (⟨.fork old A R,rest'⟩ : Cursor α (ρ × Fields ι C)))
          (next := fun entry _ => replaceChild (identifier before.rootRecord) (descriptor identifier color after) entry) rfl
        have replaced : replaceChild (identifier before.rootRecord) (descriptor identifier color after) old =
            .writeParent fresh true := replace_left identifier color _ record before after sibling sameColors
        change SourceLocalProgram.Step code .readParent ⟨.fork old A R,rest'⟩
          (replaceChild (identifier before.rootRecord) (descriptor identifier color after) old)
          ⟨.fork old A R,rest'⟩ (some old) at actual
        rw [replaced] at actual
        exact actual
      have run : Run code .goUp ⟨A,.left old R::rest'⟩ .done ⟨A,.left fresh R::rest'⟩ [old] 4 :=
        Run.next (program := code) (.nav rfl rfl) (Run.next (program := code) read
          (Run.next (program := code) (.write rfl) (Run.next (program := code) (.nav rfl rfl) (.halt rfl))))
      refine ⟨[old],4,?_,le_rfl⟩
      simpa only [A,R,old,fresh,rest',code,cursor,frames,parentId,initial,tail] using run
    | right sibling record =>
      have nodeUnique : ((Source.fork record sibling before).inventory identifier).Nodup :=
        Multiset.nodup_of_le (inventory_le_plug identifier _ rest) unique
      have distinct := child_ids_distinct identifier record sibling before nodeUnique
      let A := annotate identifier color (some (identifier record)) after
      let L := annotate identifier color (some (identifier record)) sibling
      let old := (record,fields identifier color (parentId identifier rest) (.fork record sibling before))
      let fresh := (record,fields identifier color (parentId identifier rest) (.fork record sibling after))
      have tail := frames_congr identifier color (before := .fork record sibling before)
        (after := .fork record sibling after) rfl (by simp only [Source.support,sameColors]) rest
      let rest' := frames identifier color (.fork record sibling after) rest
      let code := program (ρ := ρ) (identifier before.rootRecord) (descriptor identifier color after)
      have read : SourceLocalProgram.Step code .readParent ⟨.fork old L A,rest'⟩
          (.writeParent fresh false) ⟨.fork old L A,rest'⟩ (some old) := by
        have actual := SourceLocalProgram.Step.read (program := code) (state := .readParent)
          (cursor := (⟨.fork old L A,rest'⟩ : Cursor α (ρ × Fields ι C)))
          (next := fun entry _ => replaceChild (identifier before.rootRecord) (descriptor identifier color after) entry) rfl
        have replaced : replaceChild (identifier before.rootRecord) (descriptor identifier color after) old =
            .writeParent fresh false := replace_right identifier color _ record before after sibling sameColors distinct
        change SourceLocalProgram.Step code .readParent ⟨.fork old L A,rest'⟩
          (replaceChild (identifier before.rootRecord) (descriptor identifier color after) old)
          ⟨.fork old L A,rest'⟩ (some old) at actual
        rw [replaced] at actual
        exact actual
      have run : Run code .goUp ⟨A,.right L old::rest'⟩ .done ⟨A,.right L fresh::rest'⟩ [old] 4 :=
        Run.next (program := code) (.nav rfl rfl) (Run.next (program := code) read
          (Run.next (program := code) (.write rfl) (Run.next (program := code) (.nav rfl rfl) (.halt rfl))))
      refine ⟨[old],4,?_,le_rfl⟩
      simpa only [A,L,old,fresh,rest',code,cursor,frames,parentId,initial,tail] using run

end ParentController
end ChaCha.Paper20261030.Structural
