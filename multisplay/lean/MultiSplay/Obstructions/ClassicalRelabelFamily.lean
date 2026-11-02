import MultiSplay.Obstructions.ClassicalOrderedFamily
import MultiSplay.ClassicalSwitchExecution
import MultiSplay.Alphabet

/-! The obstruction on an arbitrary actual preferred-path alphabet.
Relabeling changes no splay step or subtree-size potential. -/

namespace MultiSplay.Obstructions.Classical

open DynamicOptimality (RawTree)
open DynamicOptimality.SearchRotation
open ChaCha.MTR.Tree
open ClassicalSwitch

@[simp] theorem potential_map {α β : Type*} (f : α → β) (tree : RawTree α) :
    potential (Auxiliary.map f tree) = potential tree := by
  induction tree <;> simp_all [Auxiliary.map,potential,Alphabet.map_size]

 theorem word_from_positions (word : List Nat) (start : Nat) :
    (List.range' start word.length).map (fun index => (word[index-start]?).getD 0) = word := by
  apply List.ext_getElem (by simp)
  intro index firstBound secondBound
  simp only [List.getElem_map,List.getElem_range',Nat.one_mul,Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem secondBound,Option.getD_some]

/-- The endpoint and lower guard are the final two actual reference keys.
The result is the exact existing classical right-to-left switch relation,
not merely an arbitrary rotation trace between equal inorder words. -/
 theorem family_on_word (s : Nat) (positive : 0 < s) (frontKeys : List Nat) (guard pivot : Nat)
    (length : (frontKeys++[guard,pivot]).length = 2^(2*s+1)-1) :
    ∃ before left finalLeft : RawTree Nat,
      before.inorder = frontKeys++[guard,pivot] ∧ finalLeft.inorder = frontKeys ∧
      Auxiliary.Splay pivot before (.node left pivot .empty) (2*s) ∧
      Auxiliary.Splay guard left (.node finalLeft guard .empty) (s-1) ∧
      Execution pivot .empty true (.guard frontKeys guard) .absent before
        (.node (.node finalLeft guard .empty) pivot .empty) .empty (3*s-1) ∧
      potential before+(s : ℝ)*Real.logb 2 6 <
        potential (.node (.node finalLeft guard .empty) pivot .empty) := by
  let word := frontKeys++[guard,pivot]
  let maximum := 2^(2*s+1)
  let label : Nat → Nat := fun index => (word[index-2]?).getD 0
  have power : 0 < maximum := by dsimp [maximum]; positivity
  have wordLength : word.length = maximum-1 := length
  have positions : maximum = frontKeys.length+3 := by simp only [word,List.length_append,List.length_cons,List.length_nil] at wordLength; omega
  have top : label maximum = pivot := by
    have place : maximum-2 = frontKeys.length+1 := by omega
    simp only [label,word,place,List.getElem?_append_right (by omega : frontKeys.length ≤ frontKeys.length+1),
      Nat.add_sub_cancel_left,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  have predecessor : label (maximum-1) = guard := by
    have place : maximum-1-2 = frontKeys.length := by omega
    simp only [label,word,place,List.getElem?_append_right le_rfl,Nat.sub_self,
      List.getElem?_cons_zero,Option.getD_some]
  obtain ⟨last,first,second,count,gain⟩ := two_splay_family s maximum positive
  let before := Auxiliary.map label (perfect (2*s+1) maximum)
  let left := Auxiliary.map label (maximumLeft s maximum)
  let finalLeft := Auxiliary.map label last
  have beforeWord : before.inorder = word := by
    rw [Alphabet.map_inorder,perfect_word (2*s+1) maximum le_rfl]
    have start : maximum+2-2^(2*s+1) = 2 := by dsimp [maximum]; omega
    rw [start,← wordLength]
    exact word_from_positions word 2
  have first' : Auxiliary.Splay pivot before (.node left pivot .empty) (2*s) := by
    simpa only [before,left,Auxiliary.map,top] using first.map label
  have second' : Auxiliary.Splay guard left (.node finalLeft guard .empty) (s-1) := by
    simpa only [left,finalLeft,Auxiliary.map,predecessor] using second.map label
  have lastWord : finalLeft.inorder = frontKeys := by
    have firstWord := first'.inorder_eq
    have secondWord := second'.inorder_eq
    rw [beforeWord] at firstWord
    simp only [inorder,List.append_nil] at firstWord secondWord
    rw [secondWord] at firstWord
    have same : frontKeys++[guard,pivot] = finalLeft.inorder++[guard,pivot] := by
      simpa only [List.append_assoc,List.singleton_append] using firstWord
    exact List.append_cancel_right same.symm
  have run : Execution pivot .empty true (.guard frontKeys guard) .absent before
      (.node (.node finalLeft guard .empty) pivot .empty) .empty (3*s-1) := by
    rw [← count,← lastWord]
    apply Execution.right
    simpa only [Auxiliary.mirror,Boundary.reflect,Auxiliary.inorder_mirror] using
      (LeftExecution.upper (incoming := (.empty : RawTree Nat)) first'.mirror second'.mirror)
  have gain' := gain
  rw [← potential_map label (perfect (2*s+1) maximum),
    ← potential_map label (.node (.node last (maximum-1) .empty) maximum .empty)] at gain'
  simp only [Auxiliary.map,top,predecessor] at gain'
  exact ⟨before,left,finalLeft,beforeWord,lastWord,first',second',run,gain'⟩

end MultiSplay.Obstructions.Classical
