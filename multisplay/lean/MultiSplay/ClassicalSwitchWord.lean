import MultiSplay.BoundarySwitch
import MultiSplay.ForestReflection
import MultiSplay.ForestRealization
import MultiSplay.SplayDeterminism

/-!
# The classical switch word with optional ancestor guards

The two boundaries describe the nearest lower and upper reference ancestors.
An absent boundary has no outside keys. A present boundary retains all the
farther ancestors on that side, as an ordered domain. The definitions below
only combine the existing common-forest events: they introduce neither a new
BST nor a second execution or cost model.

`word` uses the old preferred side. The right-to-left case is the literal
reflection of the left-to-right case, including the order of the two guard
splits. Empty tails do not delete the pivot split or its final raw join.
-/

namespace MultiSplay.ClassicalSwitch

open DynamicOptimality (RawTree)
open ChaCha.MTR.Tree (inorder rootKey)
open CommonForest

variable {α : Type*}

inductive Boundary (α : Type*) where
  | absent
  | guard (outside : List α) (key : α)

def Boundary.lowerKeys : Boundary α → List α
  | .absent => []
  | .guard outside key => outside ++ [key]

def Boundary.upperKeys : Boundary α → List α
  | .absent => []
  | .guard outside key => key :: outside

def Boundary.reflect : Boundary α → Boundary α
  | .absent => .absent
  | .guard outside key => .guard outside.reverse key

def Boundary.count : Boundary α → Nat
  | .absent => 0
  | .guard _ _ => 1

@[simp] theorem Boundary.reflect_reflect (boundary : Boundary α) :
    boundary.reflect.reflect = boundary := by
  cases boundary <;> simp [Boundary.reflect]

@[simp] theorem Boundary.lowerKeys_reflect (boundary : Boundary α) :
    boundary.reflect.lowerKeys = boundary.upperKeys.reverse := by
  cases boundary <;> simp [Boundary.reflect, Boundary.lowerKeys, Boundary.upperKeys]

@[simp] theorem Boundary.upperKeys_reflect (boundary : Boundary α) :
    boundary.reflect.upperKeys = boundary.lowerKeys.reverse := by
  cases boundary <;> simp [Boundary.reflect, Boundary.lowerKeys, Boundary.upperKeys]

@[simp] theorem Boundary.count_reflect (boundary : Boundary α) :
    boundary.reflect.count = boundary.count := by cases boundary <;> rfl

theorem Boundary.count_le_one (boundary : Boundary α) : boundary.count ≤ 1 := by
  cases boundary <;> simp [Boundary.count]

def leftWord (lower upper : Boundary α) (old incoming : List α) (pivot : α) :
    List (Event α) :=
  match lower, upper with
  | .absent, .absent => noGuardsWord old incoming pivot
  | .guard a key, .absent => noUpperWord a old incoming key pivot
  | .absent, .guard b key => noLowerWord old incoming b pivot key
  | .guard a lo, .guard b hi => leftToRightWord a old incoming b lo pivot hi

def word (oldSide : Bool) (lower upper : Boundary α) (old incoming : List α)
    (pivot : α) : List (Event α) :=
  if oldSide then
    (leftWord upper.reflect lower.reflect old.reverse incoming.reverse pivot).map Event.mirror
  else leftWord lower upper old incoming pivot

def beforeKeys (oldSide : Bool) (lower upper : Boundary α) (old : List α) (pivot : α) : List α :=
  lower.lowerKeys ++ (if oldSide then [] else old) ++ [pivot] ++
    (if oldSide then old else []) ++ upper.upperKeys

def afterKeys (oldSide : Bool) (lower upper : Boundary α) (incoming : List α) (pivot : α) : List α :=
  beforeKeys (!oldSide) lower upper incoming pivot

theorem leftWord_structural (lower upper : Boundary α) (old incoming : List α) (pivot : α) :
    structuralCount (leftWord lower upper old incoming pivot) =
      2 + 2 * lower.count + 2 * upper.count := by
  cases lower <;> cases upper <;>
    simp [leftWord, Boundary.count, leftToRightWord_structural, noLowerWord_structural,
      noUpperWord_structural, noGuardsWord_structural]

theorem word_structural (oldSide : Bool) (lower upper : Boundary α) (old incoming : List α)
    (pivot : α) : structuralCount (word oldSide lower upper old incoming pivot) =
      2 + 2 * lower.count + 2 * upper.count := by
  cases oldSide <;> simp [word, structuralCount_mirror, leftWord_structural, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]

theorem word_structural_le_six (oldSide : Bool) (lower upper : Boundary α)
    (old incoming : List α) (pivot : α) :
    structuralCount (word oldSide lower upper old incoming pivot) ≤ 6 := by
  rw [word_structural]
  have := lower.count_le_one
  have := upper.count_le_one
  omega

/-- In particular a leaf switch, whose two tails are empty, still emits at
least its pivot split and join. -/
theorem word_structural_pos (oldSide : Bool) (lower upper : Boundary α)
    (old incoming : List α) (pivot : α) :
    2 ≤ structuralCount (word oldSide lower upper old incoming pivot) := by
  rw [word_structural]
  omega

/-- A split is obtained from total standard splaying; its exact child domains
are forced by the unique occurrence of the pivot in the source inorder word. -/
theorem split_unique {tree : RawTree α} {left right : List α} {pivot : α}
    (keys : inorder tree = left ++ [pivot] ++ right) (unique : (inorder tree).Nodup) :
    ∃ l r rotations, Auxiliary.Splay pivot tree (.node l pivot r) rotations ∧
      inorder l = left ∧ inorder r = right := by
  have missing : pivot ∉ left ∧ pivot ∉ right := by
    rw [keys] at unique
    have parts : left.Nodup ∧ right.Nodup ∧ pivot ∉ left ∧ pivot ∉ right ∧
        List.Disjoint left right := by
      simpa [List.nodup_append', List.disjoint_append_left, List.disjoint_append_right,
        and_assoc, and_left_comm, and_comm] using unique
    exact ⟨parts.2.2.1,parts.2.2.2.1⟩
  obtain ⟨l,r,rotations,execution,hl,hr⟩ := exists_pointer_split keys missing
  exact ⟨l,r,rotations,execution.1,hl,hr⟩

private theorem empty_of_inorder {tree : RawTree α} (empty : inorder tree = []) : tree = .empty := by
  cases tree with
  | empty => rfl
  | node left key right => simp [inorder] at empty

/-- The actual standard pivot and guard splays realize the prescribed word
from any source auxiliary shape. No splay transcript or checkpoint shape is
assumed. The parked tail is the actual surviving child, not a rebuilt copy. -/
theorem leftWord_realize (lower upper : Boundary α) (old : List α)
    (incoming whole : RawTree α) (pivot : α)
    (keys : inorder whole = lower.lowerKeys ++ old ++ [pivot] ++ upper.upperKeys)
    (unique : (inorder whole).Nodup) :
    ∃ after parked work,
      SplayTrace [whole,incoming] (leftWord lower upper old (inorder incoming) pivot)
        [after,parked] work ∧
      rootKey after = some pivot ∧ inorder parked = old ∧
      inorder after = lower.lowerKeys ++ [pivot] ++ inorder incoming ++ upper.upperKeys := by
  obtain ⟨left,right,pivotWork,pivotSplay,leftKeys,rightKeys⟩ :=
    split_unique (left := lower.lowerKeys ++ old) (by simpa [List.append_assoc] using keys) unique
  have afterUnique : (inorder (.node left pivot right)).Nodup := pivotSplay.inorder_eq ▸ unique
  have leftUnique := (Auxiliary.nodup_node afterUnique).1
  have rightUnique := (Auxiliary.nodup_node afterUnique).2.1
  cases lower with
  | absent =>
      simp only [Boundary.lowerKeys, List.nil_append] at leftKeys
      cases upper with
      | absent =>
          have rightEmpty := empty_of_inorder rightKeys
          subst right
          refine ⟨.node .empty pivot incoming,left,pivotWork+2,?_,rfl,leftKeys,?_⟩
          · simpa [leftWord, leftKeys] using noGuards_exact (incoming := incoming) pivotSplay
          · simp [inorder, Boundary.lowerKeys, Boundary.upperKeys]
      | guard b hi =>
          obtain ⟨vacant,bTree,upperWork,upperSplay,emptyKeys,bKeys⟩ :=
            split_unique (left := []) (by simpa [Boundary.upperKeys] using rightKeys) rightUnique
          have isEmpty := empty_of_inorder emptyKeys
          subst vacant
          refine ⟨.node .empty pivot (.node incoming hi bTree),left,pivotWork+upperWork+4,
            ?_,rfl,leftKeys,?_⟩
          · simpa [leftWord, leftKeys, bKeys] using noLower_exact (incoming := incoming) pivotSplay upperSplay
          · simp [inorder, Boundary.lowerKeys, Boundary.upperKeys, bKeys, List.append_assoc]
  | guard a lo =>
      obtain ⟨aTree,oldTree,lowerWork,lowerSplay,aKeys,oldKeys⟩ :=
        split_unique (by simpa [Boundary.lowerKeys, List.append_assoc] using leftKeys) leftUnique
      cases upper with
      | absent =>
          have rightEmpty := empty_of_inorder rightKeys
          subst right
          refine ⟨.node (.node aTree lo .empty) pivot incoming,oldTree,pivotWork+lowerWork+4,
            ?_,rfl,oldKeys,?_⟩
          · simpa [leftWord, aKeys, oldKeys] using noUpper_exact (incoming := incoming) pivotSplay lowerSplay
          · simp [inorder, Boundary.lowerKeys, Boundary.upperKeys, aKeys, List.append_assoc]
      | guard b hi =>
          obtain ⟨vacant,bTree,upperWork,upperSplay,emptyKeys,bKeys⟩ :=
            split_unique (left := []) (by simpa [Boundary.upperKeys] using rightKeys) rightUnique
          have isEmpty := empty_of_inorder emptyKeys
          subst vacant
          refine ⟨.node (.node aTree lo .empty) pivot (.node incoming hi bTree),oldTree,
            pivotWork+lowerWork+upperWork+6,?_,rfl,oldKeys,?_⟩
          · simpa [leftWord, aKeys, oldKeys, bKeys] using
              leftToRight_exact (incoming := incoming) pivotSplay lowerSplay upperSplay
          · simp [inorder, Boundary.lowerKeys, Boundary.upperKeys, aKeys, bKeys, List.append_assoc]

@[simp] theorem rootKey_mirror (tree : RawTree α) :
    rootKey (Auxiliary.mirror tree) = rootKey tree := by cases tree <;> rfl

/-- Both switch directions, with any combination of missing ancestor guards.
The output root is the switched original key even when both tails are empty. -/
theorem word_realize (oldSide : Bool) (lower upper : Boundary α) (old : List α)
    (incoming whole : RawTree α) (pivot : α)
    (keys : inorder whole = beforeKeys oldSide lower upper old pivot)
    (unique : (inorder whole).Nodup) :
    ∃ after parked work,
      SplayTrace [whole,incoming] (word oldSide lower upper old (inorder incoming) pivot)
        [after,parked] work ∧
      rootKey after = some pivot ∧ inorder parked = old ∧
      inorder after = afterKeys oldSide lower upper (inorder incoming) pivot := by
  cases oldSide with
  | false =>
      simpa [word, beforeKeys, afterKeys, List.append_assoc] using
        leftWord_realize lower upper old incoming whole pivot
          (by simpa [beforeKeys, List.append_assoc] using keys) unique
  | true =>
      have reflectedKeys : inorder (Auxiliary.mirror whole) =
          upper.reflect.lowerKeys ++ old.reverse ++ [pivot] ++ lower.reflect.upperKeys := by
        rw [Auxiliary.inorder_mirror, keys]
        simp [beforeKeys, List.reverse_append, List.append_assoc]
      have reflectedUnique : (inorder (Auxiliary.mirror whole)).Nodup := by
        simpa only [Auxiliary.inorder_mirror, List.nodup_reverse] using unique
      obtain ⟨after,parked,work,run,root,oldKeys,newKeys⟩ :=
        leftWord_realize upper.reflect lower.reflect old.reverse
          (Auxiliary.mirror incoming) (Auxiliary.mirror whole) pivot reflectedKeys reflectedUnique
      refine ⟨Auxiliary.mirror after, Auxiliary.mirror parked, work, ?_, ?_, ?_, ?_⟩
      · simpa [word, Auxiliary.inorder_mirror] using run.mirror
      · simpa only [rootKey_mirror] using root
      · simp only [Auxiliary.inorder_mirror, oldKeys, List.reverse_reverse]
      · rw [Auxiliary.inorder_mirror, newKeys]
        simp [afterKeys, beforeKeys, Auxiliary.inorder_mirror, List.reverse_append, List.append_assoc]

end MultiSplay.ClassicalSwitch
