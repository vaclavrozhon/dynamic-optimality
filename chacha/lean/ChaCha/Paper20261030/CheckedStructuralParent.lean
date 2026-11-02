import ChaCha.Paper20261030.StructuralReadiness

/-! Readiness of the external-parent repair. Before its first ascent,
the external parent's child identifier can still refer to the old root.
Only the unchanged child color masks are used by that ascent. The return
descent occurs after the child identifier has been rewritten.
-/

namespace ChaCha.Paper20261030.Structural.ParentController

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

theorem checked_repair (identifier : ρ → ι) (color : α → C) (before after : Source α ρ)
    (sameColors : before.support color = after.support color) (outside : List (Frame α ρ))
    (unique : ((plug before outside).inventory identifier).Nodup) :
    ∃ reads cost,
      CheckedRun identifier color (program (identifier before.rootRecord) (descriptor identifier color after))
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
      have run : CheckedRun identifier color code .goUp ⟨A,.left old R::rest'⟩ .done ⟨A,.left fresh R::rest'⟩ [old] 4 :=
        CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,A,R,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors]) (CheckedRun.next (program := code) read (by simp [code,program,Ready,Children,Parent,A,R,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors])
          (CheckedRun.next (program := code) (.write rfl) (by simp [code,program,Ready,Children,Parent,A,R,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors]) (CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,A,R,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors]) (.halt rfl))))
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
      have run : CheckedRun identifier color code .goUp ⟨A,.right L old::rest'⟩ .done ⟨A,.right L fresh::rest'⟩ [old] 4 :=
        CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,A,L,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors]) (CheckedRun.next (program := code) read (by simp [code,program,Ready,Children,Parent,A,L,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors])
          (CheckedRun.next (program := code) (.write rfl) (by simp [code,program,Ready,Children,Parent,A,L,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors]) (CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,A,L,old,fresh,fields,descriptor,annotate_root,annotate_support,Source.setRoot,Source.rootRecord.eq_1,Source.rootRecord.eq_2,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,sameColors]) (.halt rfl))))
      refine ⟨[old],4,?_,le_rfl⟩
      simpa only [A,L,old,fresh,rest',code,cursor,frames,parentId,initial,tail] using run

end ChaCha.Paper20261030.Structural.ParentController
