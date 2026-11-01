import MultiSplay.InterfaceDetach

/-!
# Returning detached component roots to neutral value

The trace performs every unit decrease explicitly. Conversion alone never
changes an interface value. Blocks and their histories are unchanged by these
decreases; only the selected root value is returned to one.
-/

namespace MultiSplay.InterfaceForest

open Splay.Interface

variable {n : Nat}

@[simp] theorem setValue_self (state : State n) (element : Element n) :
    setValue state element (state.value element) = state := by
  cases state
  simp [setValue]

@[simp] theorem setValue_twice (state : State n) (element : Element n) (first last : Nat) :
    setValue (setValue state element first) element last = setValue state element last := by
  simp [setValue, Function.update_idem]

def neutralizeWord (state : State n) (element : Element n) : List (Operation n) :=
  List.replicate (state.value element - 1) (.valueChange element .decrease)

theorem neutralize_trace_aux {params : Parameters} (count : Nat) (state : State n) (element : Element n)
    (valid : state.Valid params) (value : state.value element = count + 1) :
    Trace params state (List.replicate count (.valueChange element .decrease)) (setValue state element 1) := by
  induction count generalizing state with
  | zero =>
      have same : setValue state element 1 = state := by simpa only [value] using setValue_self state element
      rw [same]
      exact .nil valid
  | succ count ih =>
      have first := decrease_step state element valid (by omega)
      have afterValue : (setValue state element (state.value element - 1)).value element = count + 1 := by
        simp only [setValue, Function.update_self]
        omega
      have rest := ih _ first.2.2 afterValue
      simpa only [List.replicate_succ, setValue_twice] using Trace.cons first rest

theorem neutralize_trace {params : Parameters} (state : State n) (element : Element n)
    (valid : state.Valid params) :
    Trace params state (neutralizeWord state element) (setValue state element 1) := by
  apply neutralize_trace_aux
  · exact valid
  · have bound := (valid.2.1 element).1
    omega

@[simp] theorem neutralize_inserts (state : State n) (element : Element n) :
    totalInserts (neutralizeWord state element) = 0 := by
  simp [neutralizeWord, totalInserts, Operation.insertCount]

@[simp] theorem neutralize_increases (state : State n) (element : Element n) :
    totalIncreases (neutralizeWord state element) = 0 := by
  simp [neutralizeWord, totalIncreases, Operation.increaseCount]

@[simp] theorem neutralize_activity (state : State n) (element : Element n) :
    totalActivity (neutralizeWord state element) = 0 := by
  simp [neutralizeWord, totalActivity, Operation.activity]

@[simp] theorem neutralize_decreases (state : State n) (element : Element n) :
    totalDecreases (neutralizeWord state element) = state.value element - 1 := by
  simp [neutralizeWord, totalDecreases, Operation.decreaseCount]

def detachNeutral (state : State n) (id : BlockId) (child : Element n) : State n :=
  setValue (delete state id child) child 1

def detachNeutralWord (state : State n) (id : BlockId) (child : Element n) : List (Operation n) :=
  [.delete id child] ++ neutralizeWord state child

theorem detachNeutral_trace {params : Parameters} (state : State n) (id : BlockId) (block : Block n)
    (child : Element n) (valid : state.Valid params) (found : state.block? id = some block)
    (shrinking : block.mode = .shrinking) (present : child ∈ block.elements) :
    Trace params state (detachNeutralWord state id child) (detachNeutral state id child) := by
  have first := delete_step state id block child valid found shrinking present
  have rest := neutralize_trace (delete state id child) child first.2.2
  exact .cons first rest

end MultiSplay.InterfaceForest
