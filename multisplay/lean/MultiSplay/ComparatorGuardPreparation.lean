import MultiSplay.ComparatorGuardPath
import MultiSplay.ComparatorReconfiguration
import MultiSplay.ComparatorCheckpoints
import MultiSplay.ClassicalSwitchWord

/-!
# Guard preparation preserves the complete opaque frontier

A displayed pivot and guards are original keys of the rooted skeleton.
Preparing their prescribed shape uses only shallow skeleton rotations.
Every original off-skeleton subtree remains in the same inorder gap.
The bound charges the skeleton, never the sizes of the opaque payloads.
-/

namespace MultiSplay.ComparatorGuard

open DynamicOptimality (RawTree)
open ChaCha.MTR
open ChaCha.MTR.Tree (inorder size plug)
open CommonForest

variable {α : Type*}

/-- Expose an actual selected pivot while retaining the literal gap array. -/
theorem split_hull (before : RawTree α) (leftKeys rightKeys : List α) (pivot : α)
    (keys : before.inorder = leftKeys ++ [pivot] ++ rightKeys)
    (unique : before.inorder.Nodup) (gaps : Nat → RawTree α) (offset : Nat) :
    ∃ left right : RawTree α, left.inorder = leftKeys ∧ right.inorder = rightKeys ∧
      ∃ work ≤ 12*before.size,
        Program [plug gaps offset before] []
          [.node (plug gaps offset left) pivot (plug gaps (offset+left.size+1) right)] work := by
  obtain ⟨left,right,rotations,run,leftKeysEq,rightKeysEq⟩ := ClassicalSwitch.split_unique keys unique
  obtain ⟨work,bound,program⟩ := rooted_hull_program before (ChaCha.MTR.Tree.node left pivot right) run.inorder_eq gaps offset
  have sizes : before.size = (ChaCha.MTR.Tree.node left pivot right).size := by
    simpa only [Tree.length_inorder] using congrArg List.length run.inorder_eq
  exact ⟨left,right,leftKeysEq,rightKeysEq,work,by omega,program⟩

/-- Three present guards determine an actual skeleton of the checkpoint
shape. No assumptions are made about the shapes within its key intervals. -/
theorem three_guard_shape (before : RawTree α) (aKeys oldKeys bKeys : List α)
    (lower pivot upper : α)
    (keys : before.inorder = aKeys ++ [lower] ++ oldKeys ++ [pivot,upper] ++ bKeys)
    (unique : before.inorder.Nodup) :
    ∃ a old b : RawTree α,
      a.inorder = aKeys ∧ old.inorder = oldKeys ∧ b.inorder = bKeys ∧
      before.inorder = (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old) pivot (ChaCha.MTR.Tree.node .empty upper b)).inorder := by
  obtain ⟨left,right,pivotRotations,pivotRun,leftWord,rightWord⟩ :=
    ClassicalSwitch.split_unique (tree := before) (pivot := pivot)
      (left := aKeys ++ [lower] ++ oldKeys) (right := upper::bKeys)
      (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using keys) unique
  have targetUnique : (ChaCha.MTR.Tree.node left pivot right).inorder.Nodup := pivotRun.inorder_eq ▸ unique
  have leftUnique : left.inorder.Nodup := targetUnique.of_append_left.of_append_left
  have rightUnique : right.inorder.Nodup := targetUnique.of_append_right
  obtain ⟨a,old,lowerRotations,lowerRun,aWord,oldWord⟩ :=
    ClassicalSwitch.split_unique leftWord leftUnique
  obtain ⟨empty,b,upperRotations,upperRun,emptyWord,bWord⟩ :=
    ClassicalSwitch.split_unique (pivot := upper) (left := []) (right := bKeys)
      (by simpa using rightWord) rightUnique
  exact ⟨a,old,b,aWord,oldWord,bWord,by
    simp only [Tree.inorder,aWord,oldWord,bWord,List.nil_append,List.append_assoc] at *
    simpa only [List.cons_append,List.nil_append] using keys⟩

/-- The complete guard preparation is linear in the displayed source hull;
its ordinary hanging subtrees may have arbitrary sizes. -/
theorem prepare_three (before : RawTree α) (aKeys oldKeys bKeys : List α)
    (lower pivot upper : α)
    (keys : before.inorder = aKeys ++ [lower] ++ oldKeys ++ [pivot,upper] ++ bKeys)
    (unique : before.inorder.Nodup) (gaps : Nat → RawTree α) (offset : Nat) :
    ∃ a old b : RawTree α,
      a.inorder = aKeys ∧ old.inorder = oldKeys ∧ b.inorder = bKeys ∧
      ∃ work ≤ 12*before.size,
        Program [plug gaps offset before] []
          [plug gaps offset (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old) pivot (ChaCha.MTR.Tree.node .empty upper b))] work := by
  obtain ⟨a,old,b,aWord,oldWord,bWord,same⟩ := three_guard_shape before aKeys oldKeys bKeys lower pivot upper keys unique
  obtain ⟨work,bound,program⟩ := rooted_hull_program before
    (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old) pivot (ChaCha.MTR.Tree.node .empty upper b)) same gaps offset
  have sizes := congrArg List.length same
  simp only [Tree.length_inorder] at sizes
  exact ⟨a,old,b,aWord,oldWord,bWord,work,by omega,program⟩

/-- Once the ordinary gap between the adjacent pivot and upper guard is
empty, the prepared physical tree has exactly the prescribed checkpoint
shape. This equation keeps all other opaque payloads verbatim. -/
theorem plug_three_shape (a old b : RawTree α) (lower pivot upper : α)
    (gaps : Nat → RawTree α) (offset : Nat)
    (emptyGap : gaps (offset+a.size+old.size+2) = .empty) :
    plug gaps offset (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old) pivot (ChaCha.MTR.Tree.node .empty upper b)) =
      .node (ChaCha.MTR.Tree.node (plug gaps offset a) lower (plug gaps (offset+a.size+1) old)) pivot
        (ChaCha.MTR.Tree.node .empty upper (plug gaps (offset+a.size+old.size+3) b)) := by
  simp only [plug,Tree.size]
  have first : offset+(a.size+1+old.size)+1 = offset+a.size+old.size+2 := by omega
  have second : offset+(a.size+1+old.size)+1+0+1 = offset+a.size+old.size+3 := by omega
  rw [first,emptyGap]

/-- Execute the exact six checkpoints after rooted-hull preparation. The
old physical tail is detached only at its prescribed split. -/
theorem prepare_checkpoints (before a old b incoming : RawTree α)
    (lower pivot upper : α)
    (same : before.inorder = (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old) pivot (ChaCha.MTR.Tree.node .empty upper b)).inorder)
    (gaps : Nat → RawTree α) (offset : Nat)
    (emptyGap : gaps (offset+a.size+old.size+2) = .empty) :
    ∃ work ≤ 12*before.size+6,
      Program [plug gaps offset before,incoming]
        (leftToRightWord (inorder (plug gaps offset a))
          (inorder (plug gaps (offset+a.size+1) old)) (inorder incoming)
          (inorder (plug gaps (offset+a.size+old.size+3) b)) lower pivot upper)
        [.node (ChaCha.MTR.Tree.node (plug gaps offset a) lower .empty) pivot
          (ChaCha.MTR.Tree.node incoming upper (plug gaps (offset+a.size+old.size+3) b)),
          plug gaps (offset+a.size+1) old] work := by
  obtain ⟨work,bound,prepare⟩ := rooted_hull_program before
    (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old) pivot (ChaCha.MTR.Tree.node .empty upper b)) same gaps offset
  have sizes := congrArg List.length same
  simp only [Tree.length_inorder] at sizes
  rw [plug_three_shape a old b lower pivot upper gaps offset emptyGap] at prepare
  have contextual := prepare.context [] [incoming]
  have checkpoints := leftToRight_checkpoints (plug gaps offset a)
    (plug gaps (offset+a.size+1) old) incoming
    (plug gaps (offset+a.size+old.size+3) b) lower pivot upper
  refine ⟨work+6,by omega,?_⟩
  simpa using contextual.append checkpoints


/-- The unique occurrence of a displayed root separates its two exact
inorder intervals. -/
theorem node_domains {left right : RawTree α} {pivot : α} {leftKeys rightKeys : List α}
    (keys : (ChaCha.MTR.Tree.node left pivot right).inorder = leftKeys ++ [pivot] ++ rightKeys)
    (unique : (ChaCha.MTR.Tree.node left pivot right).inorder.Nodup) :
    left.inorder = leftKeys ∧ right.inorder = rightKeys := by
  have parts := Auxiliary.nodup_node unique
  have split := (List.append_cons_inj_of_notMem parts.2.2.1 parts.2.2.2.1).mp
    (by simpa only [Tree.inorder,List.append_assoc,List.singleton_append] using keys)
  exact ⟨split.1,split.2.2⟩

/-- Actual adjacent keys have no opaque physical payload between them.
This includes the case where the external gap itself is empty. -/
theorem empty_between_adjacent {left middle right : RawTree α} {pivot upper : α}
    {leftKeys rightKeys : List α}
    (keys : (ChaCha.MTR.Tree.node left pivot (ChaCha.MTR.Tree.node middle upper right)).inorder =
      leftKeys ++ [pivot,upper] ++ rightKeys)
    (unique : (ChaCha.MTR.Tree.node left pivot (ChaCha.MTR.Tree.node middle upper right)).inorder.Nodup) :
    middle = .empty := by
  have rightWord := (node_domains (rightKeys := upper::rightKeys)
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using keys) unique).2
  have middleWord := (node_domains (leftKeys := []) (rightKeys := rightKeys)
    (by simpa using rightWord) (Auxiliary.nodup_node unique).2.1).1
  cases middle with
  | empty => rfl
  | node l key r => simp [Tree.inorder] at middleWord

/-- Equality of skeleton inorder words preserves the full physical inorder
word under one literal opaque gap array. -/
theorem plug_inorder_eq {before after : RawTree α} (same : before.inorder = after.inorder)
    (gaps : Nat → RawTree α) (offset : Nat) :
    (plug gaps offset before).inorder = (plug gaps offset after).inorder := by
  obtain ⟨count,bound,run⟩ := Tree.rooted_hull_rotation_linear before after same gaps offset
  exact run.inorder_eq

/-- The apparently empty checkpoint gap is derived from adjacency in the
actual original-key component; it is not an additional representation axiom. -/
theorem checkpoint_gap_empty {before a old b : RawTree α} {lower pivot upper : α}
    (same : before.inorder = (ChaCha.MTR.Tree.node (ChaCha.MTR.Tree.node a lower old)
      pivot (ChaCha.MTR.Tree.node .empty upper b)).inorder)
    (gaps : Nat → RawTree α) (offset : Nat) {leftKeys rightKeys : List α}
    (adjacent : (plug gaps offset before).inorder = leftKeys ++ [pivot,upper] ++ rightKeys)
    (unique : (plug gaps offset before).inorder.Nodup) :
    gaps (offset+a.size+old.size+2) = .empty := by
  have word := plug_inorder_eq same gaps offset
  have targetKeys := word.symm.trans adjacent
  have targetUnique := word ▸ unique
  have empty := empty_between_adjacent targetKeys targetUnique
  simp only [plug, Tree.size] at empty
  convert empty using 1 <;> congr 1 <;> omega

end MultiSplay.ComparatorGuard
