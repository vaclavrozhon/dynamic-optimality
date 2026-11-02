import ChaCha.Paper20261030.StructuralReadiness

/-! Structural payload writes satisfy each inspected-field obligation
when the immutable identifier is preserved. Child-parent repairs are
included in the checked execution, even though the identifier is unchanged.
-/

namespace ChaCha.Paper20261030.Structural.WriteController

open ColoredStorage SourcePointer SourceLocalProgram PackedReadiness

variable {α ρ ι C : Type*} [DecidableEq ι] [LinearOrder C] [Fintype C]

theorem checked_write (identifier : ρ → ι) (color : α → C) (parent : Option ι)
    (source : Source α ρ) (fresh : ρ) (outside)
    (sameId : identifier fresh = identifier source.rootRecord) :
    ∃ reads cost, CheckedRun identifier color (program identifier fresh) .start ⟨annotate identifier color parent source,outside⟩
      .done ⟨annotate identifier color parent (source.setRoot fresh),outside⟩ reads cost ∧ cost ≤ 10 := by
  cases source with
  | leaf key old =>
    refine ⟨[(annotate identifier color parent (.leaf key old)).rootRecord],2,?_,by decide⟩
    exact CheckedRun.next (program := program identifier fresh) (.read rfl) (by simp [program,Ready,annotate,fields,Source.rootRecord,SourceLocalProgram.isLeaf,Source.setRoot] at * <;> assumption)
      (CheckedRun.next (program := program identifier fresh) (.write rfl) (by simp [program,Ready,annotate,fields,Source.rootRecord,SourceLocalProgram.isLeaf,Source.setRoot] at * <;> assumption) (.halt rfl))
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
    have finish : CheckedRun identifier color code .upRight ⟨R',.right L' newRoot::outside⟩ .done
        ⟨.fork newRoot L' R',outside⟩ [] 1 :=
      CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r) (.halt rfl)
    have rightWrite : CheckedRun identifier color code (.writeRight (reparent (some (identifier fresh)) R.rootRecord))
        ⟨R,.right L' newRoot::outside⟩ .done ⟨.fork newRoot L' R',outside⟩ [] 2 := by
      apply CheckedRun.next (program := code) (.write rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
      simpa only [rightRoot] using finish
    have rightRun : CheckedRun identifier color code .upLeft ⟨L',.left newRoot R::outside⟩ .done
        ⟨.fork newRoot L' R',outside⟩ [R.rootRecord] 5 :=
      CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
        (CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
          (CheckedRun.next (program := code) (.read rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r) rightWrite))
    have leftWrite : CheckedRun identifier color code (.writeLeft (reparent (some (identifier fresh)) L.rootRecord))
        ⟨L,.left newRoot R::outside⟩ .done ⟨.fork newRoot L' R',outside⟩ [R.rootRecord] 6 := by
      apply CheckedRun.next (program := code) (.write rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
      simpa only [leftRoot] using rightRun
    refine ⟨[oldRoot,L.rootRecord,R.rootRecord],10,?_,le_rfl⟩
    change CheckedRun identifier color code .start ⟨.fork oldRoot L R,outside⟩ .done
      ⟨.fork newRoot L' R',outside⟩ [oldRoot,L.rootRecord,R.rootRecord] 10
    exact CheckedRun.next (program := code) (.read rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
      (CheckedRun.next (program := code) (.write rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
        (CheckedRun.next (program := code) (.nav rfl rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r)
          (CheckedRun.next (program := code) (.read rfl) (by simp [code,program,Ready,Children,Parent,L,R,L',R',oldRoot,newRoot,annotate,annotate_root,annotate_support,fields,descriptor,Source.rootRecord.eq_1,Source.rootRecord.eq_2,Source.setRoot,Source.support,Compiler.isLeaf_annotate,fields_children_leaf,SourceLocalProgram.isLeaf.eq_1,SourceLocalProgram.isLeaf.eq_2,reparent,Finset.union_assoc] at * <;> first | assumption | exact fields_children_leaf identifier color none l | exact fields_children_leaf identifier color none r) leftWrite)))

end ChaCha.Paper20261030.Structural.WriteController
