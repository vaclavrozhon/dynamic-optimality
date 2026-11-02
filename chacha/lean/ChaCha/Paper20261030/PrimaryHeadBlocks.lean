import ChaCha.Paper20261030.PrimaryWings
import ChaCha.Paper20261030.HeadMemorySplice

/-!
# The unchanged primary prefix and the two actual tail components

An actual primary head step has an identical prefix of exit records on
both sides. At its boundary, the old and incoming whole primary subtrees
exchange which one is the ordinary exit. This supplies the primary
meaning of the eight ordered blocks in `HeadBlockReassembly`.
-/

namespace ChaCha.Paper20261030.PrimaryWings

open PreferredProjection

variable {α : Type*} [DecidableEq α]

theorem head_exit_decomposition {x : α} {d : Nat} {before after : PrefRouter α}
    (step : PrefRouter.HeadStep x d before after) :
    ∃ (common : List (Exit α)) (old incoming : PrefRouter α) (oldRight : Bool),
      common.length = d ∧ before.terminal = old.terminal ∧ after.terminal = incoming.terminal ∧
      exits before = common ++ ⟨oldRight,incoming⟩ :: exits old ∧
      exits after = common ++ ⟨!oldRight,old⟩ :: exits incoming := by
  induction step with
  | leftRoot l r member =>
    exact ⟨[],r,l,true,rfl,rfl,rfl,rfl,rfl⟩
  | rightRoot l r notLeft member =>
    exact ⟨[],l,r,false,rfl,rfl,rfl,rfl,rfl⟩
  | leftDown r step ih =>
    obtain ⟨common,old,incoming,oldRight,length,oldEnd,newEnd,beforeWord,afterWord⟩ := ih
    refine ⟨⟨false,r⟩ :: common,old,incoming,oldRight,?_,oldEnd,newEnd,?_,?_⟩
    · simp only [List.length_cons,length]
    · simp only [exits,beforeWord,List.cons_append]
    · simp only [exits,afterWord,List.cons_append]
  | rightDown l notLeft step ih =>
    obtain ⟨common,old,incoming,oldRight,length,oldEnd,newEnd,beforeWord,afterWord⟩ := ih
    refine ⟨⟨true,l⟩ :: common,old,incoming,oldRight,?_,oldEnd,newEnd,?_,?_⟩
    · simp only [List.length_cons,length]
    · simp only [exits,beforeWord,List.cons_append]
    · simp only [exits,afterWord,List.cons_append]

def leftWord (exits : List (Exit α)) : List α :=
  (exits.filter (·.leftOfEndpoint)).flatMap (fun e => e.subtree.leaves)

def rightWord (exits : List (Exit α)) : List α :=
  ((exits.filter (fun e => !e.leftOfEndpoint)).reverse).flatMap (fun e => e.subtree.leaves)

theorem leftWord_append (a b : List (Exit α)) : leftWord (a ++ b) = leftWord a ++ leftWord b := by
  simp only [leftWord,List.filter_append,List.flatMap_append]

theorem rightWord_append (a b : List (Exit α)) : rightWord (a ++ b) = rightWord b ++ rightWord a := by
  simp only [rightWord,List.filter_append,List.reverse_append,List.flatMap_append]

theorem leaf_blocks (t : PrefRouter α) :
    t.leaves = leftWord (exits t) ++ [t.terminal] ++ rightWord (exits t) := leaf_partition t

/-- The exact old/new original-key block orders follow from the actual
exit decomposition, not from an assumed ordering of arbitrary blocks. -/
theorem primary_head_block_word (t old incoming : PrefRouter α) (common : List (Exit α)) (oldRight : Bool)
    (endpoint : t.terminal = old.terminal)
    (word : exits t = common ++ ⟨oldRight,incoming⟩ :: exits old) :
    t.leaves = leftWord common ++
      (if oldRight then
        leftWord (exits incoming) ++ [incoming.terminal] ++ rightWord (exits incoming) ++
          leftWord (exits old) ++ [old.terminal] ++ rightWord (exits old)
       else
        leftWord (exits old) ++ [old.terminal] ++ rightWord (exits old) ++
          leftWord (exits incoming) ++ [incoming.terminal] ++ rightWord (exits incoming)) ++
      rightWord common := by
  rw [leaf_blocks t,endpoint,word,leftWord_append,rightWord_append]
  cases oldRight <;>
    simp only [leftWord,rightWord,List.filter_cons,Bool.false_eq_true,if_false,if_true,
      Bool.not_false,Bool.not_true,List.reverse_cons,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,leaf_partition incoming,List.append_assoc]

end ChaCha.Paper20261030.PrimaryWings
