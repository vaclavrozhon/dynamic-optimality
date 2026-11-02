import MultiSplay.ClassicalSwitchWord

/-!
# The actual stopped splay checkpoints of a classical switch

The constructors retain the actual intermediate daughter trees. They allow a
global embedding to carry opaque gap payloads through each of the pivot and
guard splays, without reconstructing these witnesses from a flattened forest
trace. `leftExecution_exists` obtains all witnesses from the source domain and
unique keys. Its existence is not an extra algorithmic assumption.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder rootKey)
open CommonForest

variable {α : Type*}

inductive LeftExecution (pivot : α) (incoming : RawTree α) :
    Boundary α → Boundary α → RawTree α → RawTree α → RawTree α → Nat → Prop
  | neither {whole old : RawTree α} {work : Nat}
      (pivotSplay : Auxiliary.Splay pivot whole (.node old pivot .empty) work) :
      LeftExecution pivot incoming .absent .absent whole (.node .empty pivot incoming) old work
  | lower {whole left a old : RawTree α} {lo : α} {pivotWork lowerWork : Nat}
      (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot .empty) pivotWork)
      (lowerSplay : Auxiliary.Splay lo left (.node a lo old) lowerWork) :
      LeftExecution pivot incoming (.guard (inorder a) lo) .absent whole
        (.node (.node a lo .empty) pivot incoming) old (pivotWork+lowerWork)
  | upper {whole old right b : RawTree α} {hi : α} {pivotWork upperWork : Nat}
      (pivotSplay : Auxiliary.Splay pivot whole (.node old pivot right) pivotWork)
      (upperSplay : Auxiliary.Splay hi right (.node .empty hi b) upperWork) :
      LeftExecution pivot incoming .absent (.guard (inorder b) hi) whole
        (.node .empty pivot (.node incoming hi b)) old (pivotWork+upperWork)
  | both {whole left right a old b : RawTree α} {lo hi : α}
      {pivotWork lowerWork upperWork : Nat}
      (pivotSplay : Auxiliary.Splay pivot whole (.node left pivot right) pivotWork)
      (lowerSplay : Auxiliary.Splay lo left (.node a lo old) lowerWork)
      (upperSplay : Auxiliary.Splay hi right (.node .empty hi b) upperWork) :
      LeftExecution pivot incoming (.guard (inorder a) lo) (.guard (inorder b) hi) whole
        (.node (.node a lo .empty) pivot (.node incoming hi b)) old
        (pivotWork+lowerWork+upperWork)

theorem LeftExecution.trace {pivot : α} {incoming whole after parked : RawTree α}
    {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parked rotations) :
    SplayTrace [whole,incoming] (leftWord lower upper (inorder parked) (inorder incoming) pivot)
      [after,parked] (rotations + 2 + 2*lower.count + 2*upper.count) := by
  cases run with
  | neither pivotSplay => simpa [leftWord, Boundary.count] using noGuards_exact pivotSplay
  | lower pivotSplay lowerSplay =>
      simpa [leftWord, Boundary.count, Nat.add_assoc] using noUpper_exact pivotSplay lowerSplay
  | upper pivotSplay upperSplay =>
      simpa [leftWord, Boundary.count, Nat.add_assoc] using noLower_exact pivotSplay upperSplay
  | both pivotSplay lowerSplay upperSplay =>
      simpa [leftWord, Boundary.count, Nat.add_assoc] using leftToRight_exact pivotSplay lowerSplay upperSplay

theorem LeftExecution.root {pivot : α} {incoming whole after parked : RawTree α}
    {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parked rotations) :
    rootKey after = some pivot := by cases run <;> rfl

theorem LeftExecution.after_keys {pivot : α} {incoming whole after parked : RawTree α}
    {lower upper : Boundary α} {rotations : Nat}
    (run : LeftExecution pivot incoming lower upper whole after parked rotations) :
    inorder after = lower.lowerKeys ++ [pivot] ++ inorder incoming ++ upper.upperKeys := by
  cases run <;> simp [Boundary.lowerKeys, Boundary.upperKeys, inorder, List.append_assoc]

private theorem empty_of_inorder {tree : RawTree α} (empty : inorder tree = []) : tree = .empty := by
  cases tree with
  | empty => rfl
  | node left key right => simp [inorder] at empty

theorem leftExecution_exists (lower upper : Boundary α) (old : List α)
    (incoming whole : RawTree α) (pivot : α)
    (keys : inorder whole = lower.lowerKeys ++ old ++ [pivot] ++ upper.upperKeys)
    (unique : (inorder whole).Nodup) :
    ∃ after parked rotations,
      LeftExecution pivot incoming lower upper whole after parked rotations ∧ inorder parked = old := by
  obtain ⟨left,right,pivotWork,pivotSplay,leftKeys,rightKeys⟩ :=
    split_unique (left := lower.lowerKeys ++ old) (by simpa [List.append_assoc] using keys) unique
  have parts := Auxiliary.nodup_node (pivotSplay.inorder_eq ▸ unique)
  cases lower with
  | absent =>
      simp only [Boundary.lowerKeys, List.nil_append] at leftKeys
      cases upper with
      | absent =>
          have rightEmpty := empty_of_inorder rightKeys
          subst right
          exact ⟨_,left,pivotWork,.neither pivotSplay,leftKeys⟩
      | guard b hi =>
          obtain ⟨vacant,bTree,upperWork,upperSplay,emptyKeys,bKeys⟩ :=
            split_unique (left := []) (by simpa [Boundary.upperKeys] using rightKeys) parts.2.1
          have isEmpty := empty_of_inorder emptyKeys
          subst vacant
          refine ⟨.node .empty pivot (.node incoming hi bTree),left,pivotWork+upperWork,?_,leftKeys⟩
          simpa only [bKeys] using LeftExecution.upper (incoming := incoming) pivotSplay upperSplay
  | guard a lo =>
      obtain ⟨aTree,oldTree,lowerWork,lowerSplay,aKeys,oldKeys⟩ :=
        split_unique (by simpa [Boundary.lowerKeys, List.append_assoc] using leftKeys) parts.1
      cases upper with
      | absent =>
          have rightEmpty := empty_of_inorder rightKeys
          subst right
          refine ⟨.node (.node aTree lo .empty) pivot incoming,oldTree,pivotWork+lowerWork,?_,oldKeys⟩
          simpa only [aKeys] using LeftExecution.lower (incoming := incoming) pivotSplay lowerSplay
      | guard b hi =>
          obtain ⟨vacant,bTree,upperWork,upperSplay,emptyKeys,bKeys⟩ :=
            split_unique (left := []) (by simpa [Boundary.upperKeys] using rightKeys) parts.2.1
          have isEmpty := empty_of_inorder emptyKeys
          subst vacant
          refine ⟨.node (.node aTree lo .empty) pivot (.node incoming hi bTree),oldTree,
            pivotWork+lowerWork+upperWork,?_,oldKeys⟩
          simpa only [aKeys,bKeys] using
            LeftExecution.both (incoming := incoming) pivotSplay lowerSplay upperSplay

/-- The reflected constructor also reflects its actual intermediate trees;
it does not reorder the lower and upper stopped splays. -/
inductive Execution (pivot : α) (incoming : RawTree α) :
    Bool → Boundary α → Boundary α → RawTree α → RawTree α → RawTree α → Nat → Prop
  | left {lower upper : Boundary α} {whole after parked : RawTree α} {rotations : Nat}
      (run : LeftExecution pivot incoming lower upper whole after parked rotations) :
      Execution pivot incoming false lower upper whole after parked rotations
  | right {lower upper : Boundary α} {whole after parked : RawTree α} {rotations : Nat}
      (run : LeftExecution pivot (Auxiliary.mirror incoming) upper.reflect lower.reflect
        (Auxiliary.mirror whole) (Auxiliary.mirror after) (Auxiliary.mirror parked) rotations) :
      Execution pivot incoming true lower upper whole after parked rotations

theorem Execution.trace {pivot : α} {incoming whole after parked : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : Execution pivot incoming oldSide lower upper whole after parked rotations) :
    SplayTrace [whole,incoming] (word oldSide lower upper (inorder parked) (inorder incoming) pivot)
      [after,parked] (rotations + 2 + 2*lower.count + 2*upper.count) := by
  cases run with
  | left run => simpa only [word, Bool.false_eq_true, ↓reduceIte] using run.trace
  | right run =>
      simpa [word, Auxiliary.inorder_mirror, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run.trace.mirror

theorem Execution.root {pivot : α} {incoming whole after parked : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : Execution pivot incoming oldSide lower upper whole after parked rotations) :
    rootKey after = some pivot := by
  cases run with
  | left run => exact run.root
  | right run => simpa only [rootKey_mirror] using run.root

theorem Execution.after_keys {pivot : α} {incoming whole after parked : RawTree α}
    {oldSide : Bool} {lower upper : Boundary α} {rotations : Nat}
    (run : Execution pivot incoming oldSide lower upper whole after parked rotations) :
    inorder after = afterKeys oldSide lower upper (inorder incoming) pivot := by
  cases run with
  | left run => simpa [afterKeys, beforeKeys, List.append_assoc] using run.after_keys
  | right run =>
      have reflected := congrArg List.reverse run.after_keys
      simpa [Auxiliary.inorder_mirror, afterKeys, beforeKeys, List.reverse_append,
        List.append_assoc] using reflected

theorem execution_exists (oldSide : Bool) (lower upper : Boundary α) (old : List α)
    (incoming whole : RawTree α) (pivot : α)
    (keys : inorder whole = beforeKeys oldSide lower upper old pivot)
    (unique : (inorder whole).Nodup) :
    ∃ after parked rotations,
      Execution pivot incoming oldSide lower upper whole after parked rotations ∧ inorder parked = old := by
  cases oldSide with
  | false =>
      obtain ⟨after,parked,rotations,run,oldKeys⟩ := leftExecution_exists lower upper old incoming whole pivot
        (by simpa [beforeKeys, List.append_assoc] using keys) unique
      exact ⟨after,parked,rotations,.left run,oldKeys⟩
  | true =>
      have reflectedKeys : inorder (Auxiliary.mirror whole) =
          upper.reflect.lowerKeys ++ old.reverse ++ [pivot] ++ lower.reflect.upperKeys := by
        rw [Auxiliary.inorder_mirror, keys]
        simp [beforeKeys, List.reverse_append, List.append_assoc]
      have reflectedUnique : (inorder (Auxiliary.mirror whole)).Nodup := by
        simpa only [Auxiliary.inorder_mirror, List.nodup_reverse] using unique
      obtain ⟨after,parked,rotations,run,oldKeys⟩ := leftExecution_exists upper.reflect lower.reflect old.reverse
        (Auxiliary.mirror incoming) (Auxiliary.mirror whole) pivot reflectedKeys reflectedUnique
      refine ⟨Auxiliary.mirror after,Auxiliary.mirror parked,rotations,.right ?_,?_⟩
      · simpa only [Auxiliary.mirror_mirror] using run
      · simp only [Auxiliary.inorder_mirror, oldKeys, List.reverse_reverse]

end MultiSplay.ClassicalSwitch
