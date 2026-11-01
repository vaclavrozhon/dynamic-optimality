import Splay.Accounting.RibStackDigits
import Splay.Accounting.OfflineFrontierFolding

namespace Splay.Accounting.OfflineNormalForm.RibStack

open Digits OfflineConnectedSupport.FrontierFolding

def spineNodes (digits : List Digit) : ℕ := (digits.map Digit.value).sum

@[simp] theorem spineNodes_nil : spineNodes [] = 0 := rfl

@[simp] theorem spineNodes_cons (digit : Digit) (digits : List Digit) :
    spineNodes (digit :: digits) = digit.value + spineNodes digits := rfl

@[simp] theorem spineNodes_reverse (digits : List Digit) : spineNodes digits.reverse = spineNodes digits := by
  simp [spineNodes]

theorem spineNodes_le_length (digits : List Digit) : spineNodes digits ≤ 3 * digits.length := by
  induction digits with
  | nil => rfl
  | cons digit digits ih =>
      cases digit <;> simp only [spineNodes_cons, Digit.value, List.length_cons] <;> omega

/-- Read low class, high class, next low class, next high class, and so on.
The direction changes at every class boundary; its run length is its digit. -/
def foldingWord (direction : Bool) : List Digit → List Bool
  | [] => []
  | digit :: digits => List.replicate digit.value direction ++ foldingWord (!direction) digits.reverse
termination_by digits => digits.length
decreasing_by simp

theorem foldingWord_nil (direction : Bool) : foldingWord direction [] = [] := by rw [foldingWord]

theorem foldingWord_cons (direction : Bool) (digit : Digit) (digits : List Digit) :
    foldingWord direction (digit :: digits) =
      List.replicate digit.value direction ++ foldingWord (!direction) digits.reverse := by
  rw [foldingWord]

theorem length_foldingWord (direction : Bool) (digits : List Digit) :
    (foldingWord direction digits).length = spineNodes digits := by
  generalize measureEq : digits.length = measure
  induction measure using Nat.strong_induction_on generalizing direction digits with
  | h measure ih =>
      cases digits with
      | nil => simp [foldingWord_nil]
      | cons digit digits =>
          have rest := ih digits.reverse.length (by simp only [List.length_reverse, List.length_cons] at *; omega)
            (!direction) digits.reverse rfl
          simp only [foldingWord_cons, List.length_append, List.length_replicate, rest,
            spineNodes_reverse, spineNodes_cons]

theorem initialRun_replicate (direction : Bool) (count : ℕ) (word : List Bool) :
    initialRun direction (List.replicate count direction ++ word) = count + initialRun direction word := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ, initialRun, ih]; omega

theorem boundedRuns_replicate {direction : Bool} {count : ℕ} {word : List Bool}
    (bounded : BoundedRuns 3 word) (different : initialRun direction word = 0) (small : count ≤ 3) :
    BoundedRuns 3 (List.replicate count direction ++ word) := by
  induction count with
  | zero => simpa using bounded
  | succ count ih =>
      refine ⟨?_, ih (by omega)⟩
      have runBound : initialRun direction (List.replicate (count + 1) direction ++ word) ≤ 3 := by
        rw [initialRun_replicate, different]
        omega
      simpa only [List.replicate_succ, List.cons_append, HAppend.hAppend, instHAppendOfAppend,
        Append.append, List.instAppend, List.append] using runBound

theorem foldingWord_opposite_run (direction : Bool) (digits : List Digit) :
    initialRun (!direction) (foldingWord direction digits) = 0 := by
  cases digits with
  | nil => simp [foldingWord_nil, initialRun]
  | cons digit digits =>
      rw [foldingWord_cons]
      cases direction <;> cases digit <;> simp [Digit.value, List.replicate_succ, initialRun]

theorem foldingWord_boundedRuns (direction : Bool) (digits : List Digit) :
    BoundedRuns 3 (foldingWord direction digits) := by
  generalize measureEq : digits.length = measure
  induction measure using Nat.strong_induction_on generalizing direction digits with
  | h measure ih =>
      cases digits with
      | nil => simp [foldingWord_nil, BoundedRuns]
      | cons digit digits =>
          have rest := ih digits.reverse.length (by simp only [List.length_reverse, List.length_cons] at *; omega)
            (!direction) digits.reverse rfl
          rw [foldingWord_cons]
          exact boundedRuns_replicate rest (by simpa using foldingWord_opposite_run (!direction) digits.reverse)
            (by cases digit <;> decide)

end Splay.Accounting.OfflineNormalForm.RibStack
